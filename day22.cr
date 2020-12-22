require "advent"
first, second = input(2020, 22).split("\n\n")
first = first.lines[1..].map &.to_i32
second = second.lines[1..].map &.to_i32

class Array(T)
  def pop_left
    delete_at(0)
  end

  def score
    total = 0
    s = size
    each_with_index do |n, i|
      total += n * (s - i)
    end
    total
  end
end

def no_rec(deck1, deck2)
  while !deck1.empty? && !deck2.empty?
    f, s = deck1.delete_at(0), deck2.delete_at(0)
    if f > s
      deck1 << f << s
    else
      deck2 << s << f
    end
  end
  return !deck1.empty?
end

def rec(deck1, deck2)
  seen = Set({Int32, Int32}).new
  while !deck1.empty? && !deck2.empty?
    key = {deck1.score, deck2.score}
    return true if seen.includes?(key)
    seen << key

    f = deck1.delete_at(0)
    s = deck2.delete_at(0)

    p1wins = (f <= deck1.size) && (s <= deck2.size) ? rec(deck1[0..f-1], deck2[0..s-1]) : f > s
    if p1wins
      deck1 << f << s
    else
      deck2 << s << f
    end
  end
  return !deck1.empty?
end

def run(first, second, proc)
  ((proc.call(first, second)) ? first : second).score
end

def part1(input)
  run(input[0], input[1], ->no_rec(Array(Int32), Array(Int32)))
end

def part2(input)
  run(input[0], input[1], ->rec(Array(Int32), Array(Int32)))
end

puts part1({first, second}.clone)
puts part2({first, second}.clone)
