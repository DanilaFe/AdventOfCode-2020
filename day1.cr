require "advent"
INPUT = input(2020, 1).lines.map(&.chomp.to_i32) 

def part1
  input = INPUT.clone.sort!
  bottom = 0
  top = input.size - 1
  loop do
    sum = input[bottom] + input[top]
    if sum == 2020
      puts input[bottom] * input[top] 
      return
    elsif sum > 2020
      top -= 1
    else
      bottom += 1
    end
  end
end

def part2
  input = INPUT.clone
  input.each_with_index do |v, i|
    input.each_with_index do |v2, j|
      next if j == i
      input.each_with_index do |v3, k|
        next if k == j || k == i
        puts v3*v2*v if v3 + v2 + v == 2020
      end
    end
  end
end

part1
part2
