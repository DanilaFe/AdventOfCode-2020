INPUT = File.read("day5.txt").lines.map(&.chomp) 

def partition(choices, list)
  b = 0
  e = list.size
  choices.chars.each do |c|
    b = (b+e)//2 if c == 'B' || c == 'R'
    e = (b+e)//2 if c == 'F' || c == 'L'
  end

  return {b,e}
end

def get_id(str)
  col = str[0..6]
  row = str[7..]
  {partition(col, (0..127).to_a)[0], partition(row, (0..7).to_a)[0]}
end

def id(t)
  r, c = t
  r * 8 + c
end

def part1
  input = INPUT.clone
  max = input.max_of do |line|
    r, c = get_id(line)
    r * 8 + c
  end
  puts max
end

def part2
  input = INPUT.clone
  seen = Set(Int32).new
  max = input.each do |line|
    seen << id(get_id(line))
  end
  candidates = [] of Int32
  128.times do |r|
    next if r == 0 || r == 127
    8.times do |c|
      next if seen.includes? id({r, c})
      candidates << id({r,c})
    end
  end
  candidates = candidates.select do |i|
    seen.includes?(i-1) && seen.includes?(i+1)
  end
  puts candidates[0]
end

part1
part2
