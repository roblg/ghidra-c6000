#!/usr/bin/env python3
"""Build an execute-packet / delay-slot image. Usage: IMAGE [be].

Load at 0x1000, entry 0x1000, with auto-analysis. Words are encoded from
SPRUFE8B's .L/.S/.D opcode maps (Figures F-3, F-18, F-21) and NOP:

  1000     ADD.L1  A1,A0,A2      ; A2 = old A1
  1004  || ADD.S1  A2,A0,A1      ; A1 = old A2      (swap)
  1008     LDW.D1  *+A4[0],A5    ; lands after 4 delay slots
  100c     ADD.L1  A5,A0,A6      ; cycle +1: old A5
  1010     NOP     3             ; cycles +2..+4, load lands
  1014     ADD.L1  A5,A0,A7      ; loaded A5
  1018     MPY.M1  A1,A2,A8      ; 16x16 multiply, one delay slot
  101c     ADD.L1  A8,A0,A9      ; cycle +1: old A8
  1020     ADD.L1  A8,A0,A10     ; cycle +2: product
  1024     MVK.S1  3,A1
  1028     MVK.S1  -1,A3
  102c     MVK.S1  1,A13
  1030     MVK.S1  0,A12
  1034 L:  [A1] B.S1 L           ; reads A1 at issue
  1038  || ADD.L1  A1,A3,A1      ; delay slot: A1 -= 1
  103c     ADD.L1  A12,A13,A12   ; delay slot: counts passes
  1040     NOP     4             ; delay slots 2..5
  1044     MVK.S1  0,A14
  1048     B.S1    SKIP          ; unconditional
  104c     MVK.S1  7,A14         ; delay slot: runs on the taken path
  1050     NOP     4
  1054     MVK.S1  99,A14        ; never runs
  1060 SKIP: B.S2  B3
  1064     NOP     5
  1800     .word   0x11223344

C6000PacketSemanticsTest.java runs 0x1000..0x1060 in Ghidra's p-code
emulator with A0=0 A1=5 A2=7 A4=0x1800 A5=0x55 A8=0x99 and expects
A2=5 A5=A7=0x11223344 A6=0x55 A8=A10=35 A9=0x99 from the packets and delay
slots, and A1=-1 A12=4 A14=7 from the branch delay slots (the loop runs
four passes; lifted as an immediate jump it would never decrement A1).
"""

from pathlib import Path
import struct
import sys


def add_l(src1, src2, dst, p=0):
    return (dst << 23) | (src2 << 18) | (src1 << 13) | (0x03 << 5) | 0x18 | p


def add_s(src1, src2, dst, p=0):
    return (dst << 23) | (src2 << 18) | (src1 << 13) | (0x07 << 6) | 0x20 | p


def ldw_d1(base, ucst5, dst, p=0):
    # mode 0001 = *+R[ucst5], op 110 = LDW, y=0 (.D1), s=0 (A dst)
    return (dst << 23) | (base << 18) | (ucst5 << 13) | (1 << 9) | (6 << 4) | 0x4 | p


def mpy_m1(src1, src2, dst, p=0):
    # .M unit, op 11001 = MPY (signed 16 lsb x 16 lsb)
    return (dst << 23) | (src2 << 18) | (src1 << 13) | (0x19 << 7) | 0x0 | p


def nop(count):
    return (count - 1) << 13


def mvk_s1(cst, dst, p=0):
    return (dst << 23) | ((cst & 0xFFFF) << 7) | (0xA << 2) | p


def b_s1(at, target, creg=0, z=0, p=0):
    disp = (target - (at & ~31)) >> 2
    return (creg << 29) | (z << 28) | ((disp & 0x1FFFFF) << 7) | (0x4 << 2) | p


B_B3 = 0x362 | (3 << 18)

WORDS = {
    0x1000: add_l(1, 0, 2, p=1),
    0x1004: add_s(2, 0, 1),
    0x1008: ldw_d1(4, 0, 5),
    0x100C: add_l(5, 0, 6),
    0x1010: nop(3),
    0x1014: add_l(5, 0, 7),
    0x1018: mpy_m1(1, 2, 8),
    0x101C: add_l(8, 0, 9),
    0x1020: add_l(8, 0, 10),
    0x1024: mvk_s1(3, 1),
    0x1028: mvk_s1(-1, 3),
    0x102C: mvk_s1(1, 13),
    0x1030: mvk_s1(0, 12),
    0x1034: b_s1(0x1034, 0x1034, creg=4, p=1),
    0x1038: add_l(3, 1, 1),
    0x103C: add_l(13, 12, 12),
    0x1040: nop(4),
    0x1044: mvk_s1(0, 14),
    0x1048: b_s1(0x1048, 0x1060),
    0x104C: mvk_s1(7, 14),
    0x1050: nop(4),
    0x1054: mvk_s1(99, 14),
    0x1060: B_B3,
    0x1064: nop(5),
    0x1800: 0x11223344,
}


def main():
    image = Path(sys.argv[1])
    endian = ">" if len(sys.argv) > 2 and sys.argv[2] == "be" else "<"
    data = bytearray(b"\x00" * 0x1000)
    for addr, word in WORDS.items():
        struct.pack_into(endian + "I", data, addr - 0x1000, word)
    image.parent.mkdir(parents=True, exist_ok=True)
    image.write_bytes(bytes(data))


if __name__ == "__main__":
    main()
