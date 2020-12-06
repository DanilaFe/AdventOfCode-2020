require "advent"
INPUT = input(2020, 6).split("\n\n")

def part1
  input = INPUT.clone
  answers = input.map do |i|
    i.chars.uniq!.count &.ascii_letter?
  end
  puts answers.sum
end

def part2
  input = INPUT.clone
  sol = input.map do |i|
    i.split("\n").reject(&.empty?).map(&.chars.to_set).reduce { |s1, s2| s1 & s2 }
  end
  puts(sol.map(&.size).sum)
end

part1
part2
