INPUT = File.read("day2.txt").lines.map(&.chomp) 

def part1
  input = INPUT.clone
  total = 0
  input.each do |line|
    data = line.match(/([0-9]+)-([0-9]+) ([a-z]): ([a-z]+)/) 
    next unless data
    min = data[1].to_i
    max = data[2].to_i
    char = data[3][0]
    str = data[4]
    count = str.chars.count(char)
    total += 1 if count >= min && count <= max
  end

  puts total
end

def part2
  input = INPUT.clone
  total = 0
  input.each do |line|
    data = line.match(/([0-9]+)-([0-9]+) ([a-z]): ([a-z]+)/) 
    next unless data
    min = data[1].to_i - 1
    max = data[2].to_i - 1
    char = data[3][0]
    str = data[4]
    count = str.chars.count(char)
    total += 1 if ((str[min] == char) || (str[max] == char) ) && str[min] != str[max]
  end
  puts total
end

part1
part2
