require "advent"
INPUT = input(2020, 15).split(",").map(&.to_i32) 

def run(input, times)
  ls = {} of Int32 => {Int32,Int32}
  last = 0
  input.each_with_index do |n, i|
    ls[n] ||= {-1,-1}
    f,s = ls[n]
    ls[n] = {i,f}
    last = n
  end
  count = input.size
  while count < times
    n = 0
    if ls[last][1] != -1
      n = ls[last][0] - ls[last][1]
    end
    last = n
    ls[n] ||= {-1,-1}
    f,s = ls[n]
    ls[n] = {count,f}
    count += 1
  end
  last
end

def part1(input)
  run(input, 2020)
end

def part2(input)
  run(input, 30000000)
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
