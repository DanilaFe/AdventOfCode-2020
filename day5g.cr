i=File.read_lines("day5.txt").map &.tr("FBLR", "0101").to_i32(2);
puts({i.max,(i.min..i.max).select{|n|!i.includes? n}})
