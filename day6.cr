require "advent"
INPUT = input(2020, 6).split("\n\n")

def part1
  INPUT.sum &.chars.uniq!.count(&.ascii_letter?)
end

def part2
  INPUT.sum &.lines.map(&.chars.to_set).intersect.size
end

puts part1
puts part2
