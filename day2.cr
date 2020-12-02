INPUT = File.read("day2.txt").lines.map(&.chomp) 

def parse(line)
    data = line.match(/([0-9]+)-([0-9]+) ([a-z]): ([a-z]+)/) 
    data.try do |data|
      min = data[1].to_i
      max = data[2].to_i
      char = data[3][0]
      str = data[4]
      {min,max,char,str}
    end
end

def part1
  input = INPUT.clone
  total = input.count do |line|
    next false unless data = parse(line)
    min, max, char, str = data
    count = str.chars.count(char)
    count >= min && count <= max
  end

  puts total
end

def part2
  input = INPUT.clone
  total = input.count do |line|
    next false unless data = parse(line)
    min, max, char, str = data
    min -= 1
    max -= 1
    (str[min] == char) ^ (str[max] == char)
  end

  puts total
end

part1
part2
