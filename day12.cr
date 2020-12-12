require "advent"
INPUT = input(2020, 12).lines.map do |l|
  {l[0], l[1..].to_i32}
end

def part1(input)
  pos = {0, 0}
  angle = 0
  input.each do |c, n|
    case c
    when 'N'
      pos = pos.add({0, n})
    when 'S'
      pos = pos.add({0, -n})
    when 'E'
      pos = pos.add({n, 0})
    when 'W'
      pos = pos.add({-n, 0})
    when 'L'
      angle = (angle + n) % 360
    when 'R'
      angle = (angle + (360-n)) % 360
    when 'F'
      dists = [{1, 0}, {0, 1}, {-1, 0}, {0, -1}]
      dx, dy = dists[angle//90]
      pos = pos.add({dx * n, dy * n})
    end
  end
  pos.map(&.abs).sum
end

def part2(input)
  pos = {10, 1}
  spos = {0, 0}
  angle = 0
  input.each do |c, n|
    case c
    when 'N'
      pos = pos.add({0, n})
    when 'S'
      pos = pos.add({0, -n})
    when 'E'
      pos = pos.add({n, 0})
    when 'W'
      pos = pos.add({-n, 0})
    when 'L'
      (n//90).times do
        pos = {-pos[1], pos[0]}
      end
    when 'R'
      (n//90).times do
        pos = {pos[1], -pos[0]}
      end
    when 'F'
      spos = spos.add({pos[0] * n, pos[1]*n})
    end
  end
  spos.map(&.abs).sum
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
