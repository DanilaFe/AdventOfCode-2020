require "advent"
INPUT = input(2020, 11).lines.map(&.chars) 

abstract class Search
  def search(current, x, y, dx, dy)
    x, y = x + dx, y + dy
    return 0 if y < 0 || y >= current.size
    return 0 if x < 0 || x >= current[y].size
    search_impl(current,x,y,dx,dy)
  end

  abstract def search_impl(current, x, y, dx, dy)
end

class FirstSearch < Search
  def search_impl(current, x, y, dx, dy)
    return current[y][x] == '#' ? 1 : 0
  end
end

class SecondSearch < Search
  def search_impl(current, x, y, dx, dy)
    return 1 if current[y][x] == '#'
    return 0 if current[y][x] == 'L'
    return search(current, x, y, dx, dy)
  end
end

DIRS = [{-1,-1}, {-1, 0}, {-1, 1}, {0, -1}, {0, 1}, {1, -1}, {1, 0}, {1,1}]

def step(current, step, check, n)
  current.each_with_index do |row, y|
    row.each_with_index do |seat, x|
      step[y][x] = current[y][x]
      count = DIRS.sum do |dx, dy|
        check.search(current, x, y, dx, dy)
      end
      step[y][x] = 'L' if seat == '#' && count >= n
      step[y][x] = '#' if seat == 'L' && count == 0
    end
  end
  {step, current}
end

def run(input, search, n)
  current = input
  step = input.clone
  loop do
    current, step = step(current, step, search, n)
    break if current.zip_with(step) { |l, r| l == r }.all?
  end
  current.sum(&.count(&.==('#')))
end

def part1(input)
  run(input, FirstSearch.new, 4)
end

def part2(input)
  run(input, SecondSearch.new, 5)
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
