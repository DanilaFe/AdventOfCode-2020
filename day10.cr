require "advent"
INPUT = input(2020, 10).lines.map(&.to_i32).sort!

def part1(input)
  diff_1 = 0
  diff_3 = 0
  curr = 0
  input << (input.max + 3)
  input.each do |i|
    diff_1 += 1 if (i - curr) == 1
    diff_3 += 1 if (i - curr) == 3
    curr = i
  end
  puts diff_1 * diff_3
end

def count_ways(input, prev, index, mem, indent = 0)
  if m = mem[{prev, index}]?
    return m 
  end
  return 0_i64 if input[index] - prev > 3 || index >= input.size
  return 1_i64 if index == input.size - 1

  total = count_ways(input, input[index], index+1, mem, indent + 1)
  total += count_ways(input, prev, index+1, mem, indent + 1)

  mem[{prev, index}] = total
  return total
end

def part2(input)
  input << (input.max + 3)
  count_ways(input, 0, 0, {} of {Int32, Int32} => Int64)
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
