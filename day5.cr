require "advent"
INPUT = input(2020, 5).lines.map(&.chomp) 

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
  id({partition(col, (0..127).to_a)[0], partition(row, (0..7).to_a)[0]})
end

def id(t)
  t[0]*8 + t[1]
end

def part1
  input = INPUT.clone
  puts(input.max_of &->get_id(String))
end

def part2
  input = INPUT.clone
  seen = input.map &->get_id(String)
  candidates = [] of Int32
  128.times do |r|
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
