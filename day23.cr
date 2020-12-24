require "advent"

input = input(2020, 23).lines[0].chars.map &.to_i32

class Array(T)
  def get(i)
    self[i % size]
  end

  def del(i)
    delete_at(i % size)
  end
end

class Node
  property next : Node
  property int : Int32

  def initialize(@int, @next)
  end

  def insert(other : Node, n = 1)
    set_next = other
    (n-1).times { set_next = set_next.@next }
    set_next.next = @next
    @next = other
  end

  def remove(n = 1)
    curr = self
    to_return = self.next
    n.times { curr = curr.@next }
    @next = curr.@next
    to_return
  end

  def find(n)
    start = self
    while start.int != n
      start = start.next
    end
    return start
  end
  
  def to_s(n)
    return "" if n < 0
    return "#{@int} -> #{@next.to_s(n-1)}"
  end

  def includes?(n, count)
    return false if count <= 0
    return @int == n || @next.includes?(n, count-1)
  end
end

class Cups
  getter size : Int32
  getter head : Node

  def initialize(list : Array(Int32))
    @cache = {} of Int32 => Node
    h = list.delete_at(0)
    temp = uninitialized Node
    @cache[h] = @head = Node.new(h, temp)
    @size = list.size
    @local_min = list.min.as(Int32)
    @local_max = list.max.as(Int32)
    @head.next = @head
    curr = @head
    list.each do |n|
      @cache[n] = new = Node.new(n, curr.next)
      curr.insert(new)
      curr = new
    end
  end
  
  def to_s
    @head.to_s(@size)
  end

  def step
    first = @head
    after = first.remove(3)
    m = first.int - 1
    while after.includes?(m, 3) || m < @local_min
      m = (m < @local_min) ? @local_max : (m - 1)
    end
    @cache[m].insert(after, 3)
    @head = @head.next
  end
end

def play(input, count)
  cups = Cups.new input
  count.times { |n| cups.step }
  cups
end

def part1(input)
  cups = play(input.clone, 100)
  cups.head.find(1).next.to_s(cups.size - 1).gsub(" -> ", "")
end

def part2(input)
  list = input.clone
  max = input.max
  (1000000 - input.size).times do
    max += 1
    list << max
  end
  cups = play(list, 10000000)
  one = cups.head.find(1)
  one.next.int.to_i64 * one.next.next.int
end

puts "Part 1: #{part1(input)}"
puts "Part 2: #{part2(input)}"
