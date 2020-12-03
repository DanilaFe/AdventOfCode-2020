INPUT = File.read("day3.txt").lines.map(&.chomp) 

def run(input, slopes)
  prod = 1_i64
  slopes.each do |slope|
    trees = 0
    pos = 0
    line = 0
    right, down = slope
    while line < input.size
      trees += 1 if input[line][pos] == '#'
      pos = (pos + right) % input[line].size
      line += down
    end
    prod *= trees
  end
  prod
end

def part1
  puts run(INPUT, [{3,1}])
end

def part2
  puts run(INPUT, [{1,1}, {3,1}, {5,1}, {7,1}, {1,2}])
end

part1
part2
