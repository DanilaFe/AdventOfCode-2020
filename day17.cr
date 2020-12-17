require "advent"
INPUT = input(2020, 17).lines.map(&.chars) 

def part1(input)
  step = input.clone
  cubes = Set({Int32,Int32,Int32,Int32}).new
  new_cubes = Set({Int32,Int32,Int32,Int32}).new
  input.each_with_index do |row, y|
    row.each_with_index do |c, x|
      cubes << {x,y,0,0} if c == '#'
    end
  end

  6.times do |i|
    neighbor_count = {} of {Int32,Int32,Int32,Int32} => Int32
    cubes.each do |c|
      x,y,z,w = c
      (-1..1).each do |dx|
        (-1..1).each do |dy|
          (-1..1).each do |dz|
            (-1..1).each do |dw|
              next if dx == 0 && dy == 0 && dz == 0 && dw == 0
              neighbor_count[{x+dx,y+dy,z+dz,w+dw}] = (neighbor_count[{x+dx,y+dy,z+dz,w+dw}]? || 0) + 1
            end
          end
        end
      end
    end
    new_cubes.clear
    neighbor_count.each do |n, i|
      if cubes.includes?(n)
        new_cubes << n if (i == 2 || i == 3)
      elsif i == 3
        new_cubes << n
      end
    end
    new_cubes, cubes = cubes, new_cubes
  end
  cubes.size
end

def part2(input)
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
