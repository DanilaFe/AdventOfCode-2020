require "advent"
INPUT = input(2020, 15).split(",").map(&.to_i32) 

def run(input, times)
  ls = {} of Int32 => Int32
  temp = 0
  (times-1).times do |i|
    n = input[i]? || temp
    temp = i - (ls[n]? || i)
    ls[n] = i
  end
  return temp
end

def part1(input)
  run(input, 2020)
end

def part2(input)
  run(input, 30000000)
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
