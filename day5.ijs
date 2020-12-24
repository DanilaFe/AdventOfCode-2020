bs2n =: 3 : '+/ "1(|.*/\(1,(_1+#y)$2)) *"(1) 0 "."0 y'
ns =: bs2n "1 'F0B1L0R1' charsub > cutopen 1!:1 < jpath '~/projects/AoC/2020/year2020day5.txt.cache'
>./ns
(<./ns)+I.-.((<./ns)+i.#ns)e.ns
