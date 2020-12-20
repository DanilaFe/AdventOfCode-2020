require "advent"
require "benchmark"

INPUT = input(2020, 17).lines.map(&.chars) 

def solve(input, dim)
  step = input.clone
  cubes = Set(Array(Int32)).new
  new_cubes = Set(Array(Int32)).new
  input.each_with_index do |row, y|
    row.each_with_index do |c, x|
      cubes << [x,y].concat([0] * (dim-2)) if c == '#'
    end
  end

  8.times do |i|
    print '.'
    neighbor_count = Hash(Array(Int32), Int32).new(0)
    Array.product([[-1,0,1]] * dim).each do |diff|
      next if diff.all? &.==(0)
      cubes.each do |c|
        neighbor_count[c.zip_with(diff) { |a,b| a+b }] += 1
      end
    end

    new_cubes.clear
    neighbor_count.each do |n, i|
      new_cubes << n if i == 3 || (cubes.includes?(n) && i == 2)
    end
    new_cubes, cubes = cubes, new_cubes
  end
  cubes.size
end

def part1(input)
  solve(input, 3)
end

def part2(input)
  solve(input, 4)
end

(3..).each do |i|
  print "Dim #{i} "
  bm = Benchmark.measure { puts " #{solve(INPUT, i)}" }
  puts bm.real * 1000
end
