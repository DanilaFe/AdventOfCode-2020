require "advent"
INPUT = input(2020, 9).lines.map(&.to_i64) 

def is_sum(is, from, to, n)
  if to <= from
    return n == 0_i64
  end
  return is_sum(is, from, to-1, n) || is_sum(is, from, to-1, n-is[to-1])
end

def part1(input)
  is = input
  i = 25
  loop do
    return is[i] unless is_sum(is, i-25, i, is[i])
    i += 1
  end
end

def part2(input, i)
  input.each_with_index do |e, j|
    next if e == i
    acc = i-e
    k = j
    while acc > 0
      k += 1
      acc -= input[k]
    end
    if acc == 0
      min, max = input[j..k].minmax
      return min+max
    end
  end
end

p1 = part1(INPUT.clone)
puts part2(INPUT.clone, p1)
