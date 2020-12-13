require "advent"
INPU = input(2020, 13).lines
INPUT = {INPU[0].to_i32, INPU[1].split(",")}

def part1(input)
  early, busses = input
  busses.reject! &.==("x")
  busses = busses.map &.to_i32
  bbus = busses.min_by do |b|
    (early / b).ceil * b
  end
  diff = bbus * (((early/bbus).ceil * bbus).to_i32 - early)
end

def part2(input)
  _, busses = input
  busses = busses.map_with_index do |x, i|
    x.to_i32?.try { |n| { n, i } }
  end
  busses = busses.compact
  n = 0_i64
  iter = 1_i64
  busses.each do |m, i|
    while (n + i) % m != 0
      n += iter
    end
    iter *= m
  end
  puts n
  puts busses
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
