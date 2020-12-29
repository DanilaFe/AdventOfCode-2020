require "advent"
INPUT = input(2020, 25).lines.map(&.to_i64) 

def transform(s)
  i = 1_i64
  c = 0
  loop do
    c += 1
    i = (i * s) % 20201227
    yield i, c
  end
end

def find_size(s, goal)
  transform(s) do |n, c|
    return c if n == goal
  end
end

def part1(input)
  goal = find_size(7, input[0])
  puts goal
  transform(input[1]) do |n, c|
    return n if c == goal
  end
end

puts part1(INPUT.clone)
