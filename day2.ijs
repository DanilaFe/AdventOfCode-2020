r =: >"1 cut each cutopen 1!:1 < jpath '~/projects/AoC/2020/year2020day2.txt.cache'
rs =: >0".each'-'cut"1>(0}"1 r)
cs =: 0{"1>1{"1 r
ss =: 2{"1 r
+/1>**/|:rs-+/"1 cs=>ss
+/1=+/|:(rs-1){"1 cs=>ss
