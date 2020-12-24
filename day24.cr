require "advent"

INPUT = input(2020, 24).lines.map &.tiles.map { |t| MATCHES[t] }
MATCHES = { "se" => {0.5, -1.0}, "sw" => {-0.5, -1.0}, "ne" => {0.5, 1.0}, "nw" => {-0.5, 1.0}, "e" => {1.0, 0.0}, "w" => {-1.0, 0.0} }

class String
  def tiles
    i = 0
    tiles = [] of String
    while i < size
      if self[i] == 's' || self[i] == 'n'
        tiles << self[i..i+1] 
        i += 2
      else
        tiles << self[i..i]
        i += 1
      end
    end
    tiles
  end
end

class Array(T)
  def pos
    curr = {0.0, 0.0}
    each do |c|
      curr = curr.add c
    end
    curr
  end
end

def part1(input)
  counts = Hash({Float64,Float64}, Int32).new(0)
  input.each do |i|
    counts[i.pos] += 1
  end
  counts.count &.[1].%(2).==(1)
end

struct Tuple(*T)
  def neighbors
    MATCHES.values.map &.add(self)
  end
end

def part2(input)
  state = Hash({Float64,Float64}, Bool).new(false)
  counts = Hash({Float64,Float64}, Int32).new(0)

  input.each do |i|
    state[i.pos] ^= true
  end

  100.times do |i|
    counts.clear
    state.each do |t, f|
      next unless f
      t.neighbors.each do |n|
        counts[n] += 1
      end
    end

    new_state = state.clone.clear
    state.each do |k, v|
      next unless v
      new_state[k] = !(counts[k] == 0 || (counts[k] > 2))
    end
    counts.each do |k, v|
      new_state[k] = true if (!state[k]) && v == 2
    end
    state = new_state
  end
  state.count &.[1]
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
