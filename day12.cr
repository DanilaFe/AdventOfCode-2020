require "advent"
DISTS = [{1, 0}, {0, 1}, {-1, 0}, {0, -1}]
INPUT = input(2020, 12).lines.map do |l|
  {l[0], l[1..].to_i32}
end

def part1(input)
  pos = {0, 0}
  angle = 0
  input.each do |c, n|
    case c
    when 'N' then pos = pos.add({0, n})
    when 'S' then pos = pos.add({0, -n})
    when 'E' then pos = pos.add({n, 0})
    when 'W' then pos = pos.add({-n, 0})
    when 'L' then angle = (angle + n) % 360
    when 'R' then angle = (angle + (360-n)) % 360
    when 'F'
      dx, dy = DISTS[angle//90]
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
    when 'N' then pos = pos.add({0, n})
    when 'S' then pos = pos.add({0, -n})
    when 'E' then pos = pos.add({n, 0})
    when 'W' then pos = pos.add({-n, 0})
    when 'L' then (n//90).times { pos = {-pos[1], pos[0]} }
    when 'R' then (n//90).times { pos = {pos[1], -pos[0]} }
    when 'F' then spos = spos.add({pos[0] * n, pos[1]*n})
    end
  end
  spos.map(&.abs).sum
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
