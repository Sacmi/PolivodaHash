package main

import (
	"fmt"
	"golang.org/x/crypto/sha3"
	"hash"
	"io"
	"log"
	"net"
	"sha3-512/keccak"
	"strconv"
	"time"
	"unsafe"
)

func xorInUnaligned(d *state, buf []byte) {
	n := len(buf)
	bw := (*[maxRate / 8]uint64)(unsafe.Pointer(&buf[0]))[: n/8 : n/8]
	if n >= 72 {
		d.a[0] ^= bw[0]
		d.a[1] ^= bw[1]
		d.a[2] ^= bw[2]
		d.a[3] ^= bw[3]
		d.a[4] ^= bw[4]
		d.a[5] ^= bw[5]
		d.a[6] ^= bw[6]
		d.a[7] ^= bw[7]
		d.a[8] ^= bw[8]
	}
	if n >= 104 {
		d.a[9] ^= bw[9]
		d.a[10] ^= bw[10]
		d.a[11] ^= bw[11]
		d.a[12] ^= bw[12]
	}
	if n >= 136 {
		d.a[13] ^= bw[13]
		d.a[14] ^= bw[14]
		d.a[15] ^= bw[15]
		d.a[16] ^= bw[16]
	}
	if n >= 144 {
		d.a[17] ^= bw[17]
	}
	if n >= 168 {
		d.a[18] ^= bw[18]
		d.a[19] ^= bw[19]
		d.a[20] ^= bw[20]
	}
}

func copyOutUnaligned(d *state, buf []byte) {
	ab := (*[maxRate]uint8)(unsafe.Pointer(&d.a[0]))
	copy(buf, ab[:])
}

var (
	xorIn   = xorInUnaligned
	copyOut = copyOutUnaligned
)

const (
	spongeAbsorbing int = iota
	spongeSqueezing
	maxRate = 168
)

type storageBuf [maxRate / 8]uint64

type state struct {
	a      [25]uint64
	buf    []byte
	rate   int
	dsbyte byte

	storage storageBuf

	outputLen int
	state     int
}

func (b *storageBuf) asBytes() *[maxRate]byte {
	return (*[maxRate]byte)(unsafe.Pointer(b))
}

func (d *state) BlockSize() int { return d.rate }

func (d *state) Size() int { return d.outputLen }

func (d *state) Reset() {
	// Zero the permutation's state.
	for i := range d.a {
		d.a[i] = 0
	}
	d.state = spongeAbsorbing
	d.buf = d.storage.asBytes()[:0]
}

func (d *state) clone() *state {
	ret := *d
	if ret.state == spongeAbsorbing {
		ret.buf = ret.storage.asBytes()[:len(ret.buf)]
	} else {
		ret.buf = ret.storage.asBytes()[d.rate-cap(d.buf) : d.rate]
	}

	return &ret
}

// permute applies the KeccakF-1600 permutation. It handles
// any input-output buffering.
func (d *state) permute() {
	switch d.state {
	case spongeAbsorbing:
		// If we're absorbing, we need to xor the input into the state
		// before applying the permutation.
		xorIn(d, d.buf)
		d.buf = d.storage.asBytes()[:0]
		keccak.KeccakF1600(&d.a)
	case spongeSqueezing:
		// If we're squeezing, we need to apply the permutation before
		// copying more output.
		keccak.KeccakF1600(&d.a)
		d.buf = d.storage.asBytes()[:d.rate]
		copyOut(d, d.buf)
	}
}

// pads appends the domain separation bits in dsbyte, applies
// the multi-bitrate 10..1 padding rule, and permutes the state.
func (d *state) padAndPermute(dsbyte byte) {
	if d.buf == nil {
		d.buf = d.storage.asBytes()[:0]
	}
	// Pad with this instance's domain-separator bits. We know that there's
	// at least one byte of space in d.buf because, if it were full,
	// permute would have been called to empty it. dsbyte also contains the
	// first one bit for the padding. See the comment in the state struct.
	d.buf = append(d.buf, dsbyte)
	zerosStart := len(d.buf)
	d.buf = d.storage.asBytes()[:d.rate]
	for i := zerosStart; i < d.rate; i++ {
		d.buf[i] = 0
	}
	// This adds the final one bit for the padding. Because of the way that
	// bits are numbered from the LSB upwards, the final bit is the MSB of
	// the last byte.
	d.buf[d.rate-1] ^= 0x80
	// Apply the permutation
	d.permute()
	d.state = spongeSqueezing
	d.buf = d.storage.asBytes()[:d.rate]
	copyOut(d, d.buf)
}

func (d *state) Write(p []byte) (written int, err error) {
	if d.state != spongeAbsorbing {
		panic("sha3: write to sponge after read")
	}
	if d.buf == nil {
		d.buf = d.storage.asBytes()[:0]
	}
	written = len(p)

	for len(p) > 0 {
		if len(d.buf) == 0 && len(p) >= d.rate {
			// The fast path; absorb a full "rate" bytes of input and apply the permutation.
			xorIn(d, p[:d.rate])
			p = p[d.rate:]
			keccak.KeccakF1600(&d.a)
		} else {
			// The slow path; buffer the input until we can fill the sponge, and then xor it in.
			todo := d.rate - len(d.buf)
			if todo > len(p) {
				todo = len(p)
			}
			d.buf = append(d.buf, p[:todo]...)
			p = p[todo:]

			// If the sponge is full, apply the permutation.
			if len(d.buf) == d.rate {
				d.permute()
			}
		}
	}

	return
}

// Read squeezes an arbitrary number of bytes from the sponge.
func (d *state) Read(out []byte) (n int, err error) {
	// If we're still absorbing, pad and apply the permutation.
	if d.state == spongeAbsorbing {
		d.padAndPermute(d.dsbyte)
	}

	n = len(out)

	// Now, do the squeezing.
	for len(out) > 0 {
		n := copy(out, d.buf)
		d.buf = d.buf[n:]
		out = out[n:]

		// Apply the permutation if we've squeezed the sponge dry.
		if len(d.buf) == 0 {
			d.permute()
		}
	}

	return
}

func (d *state) Sum(in []byte) []byte {
	// Make a copy of the original hash so that caller can keep writing
	// and summing.
	dup := d.clone()
	hash := make([]byte, dup.outputLen)
	dup.Read(hash)
	return append(in, hash...)
}

func New512() hash.Hash {
	return &state{rate: 72, outputLen: 64, dsbyte: 0x06}
}

// Вычисление хеша сообщения
func encode(message string) []byte {
	messageBytes := []byte(message)

	h := New512()
	h.Write(messageBytes)

	digest := h.Sum(messageBytes)
	bytes := sha3.Sum512(messageBytes)

	fmt.Println("Полученный хеш: ", bytes)
	_ = digest

	return append(bytes[:], messageBytes[:]...)
}

func reader(r io.Reader) {
	buf := make([]byte, 1024)
	for {
		n, err := r.Read(buf[:])
		if err != nil {
			return
		}
		println("Client got:", string(buf[0:n]))
	}
}

func main() {
	// Открываю сокет
	c, err := net.Dial("unix", "/var/sockets/sha3512.sock")
	if err != nil {
		panic(err)
	}
	defer c.Close()

	go reader(c)
	i := 0

	for {
		println("Отправляю:", "Поливода "+strconv.Itoa(i))

		// Отправка сообщения и вычисление хеша
		_, err := c.Write(encode("Поливода " + strconv.Itoa(i)))
		if err != nil {
			log.Fatal("write error:", err)
			break
		}

		// Чтоб спама не было
		time.Sleep(1e9)

		i++
	}
}
