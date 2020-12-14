require "advent"
raw = input(2020, 14).lines
input = [] of {UInt64, UInt64, Array(Int32), UInt64, UInt64}

and_mask = (2_u64**63) + (2_u64**63-1)
or_mask = 0_u64
floats = [] of Int32

raw.each do |line|
  if data = line.match(/^mask = (.+)$/)
    new_mask = data[1]
    and_mask = (2_u64**63) + (2_u64**63-1)
    or_mask = 0_u64
    floats = [] of Int32
    new_mask.reverse.chars.each_with_index do |c, i|
      floats << i if c == 'X'
      or_mask = or_mask | (1_u64 << i) if c == '1'
      and_mask = and_mask & ~(1_u64 << i) if c == '0'
    end
  elsif data = line.match(/^mem\[(\d+)\] = (\d+)$/)
    input << {and_mask, or_mask, floats, data[1].to_u64, data[2].to_u64}
  else
    raise "Invalid line"
  end
end

def part1(input)
  memory = {} of UInt64 => UInt64
  input.each do |i|
    and_mask, or_mask, floats, addr, v = i
    memory[addr] = (v & and_mask) | or_mask
  end
  memory.values.sum
end

def generate_possible(indices, index, n, &block : UInt64 -> _)
  if index == indices.size
    yield n
    return 
  end
  float_addr = indices[index]
  no = n | (1_u64 << float_addr)
  generate_possible(indices, index+1, no, &block)
  nz = n & ~(1_u64 << float_addr)
  generate_possible(indices, index+1, nz, &block)
end

def part2(input)
  memory = {} of UInt64 => UInt64
  input.each do |i|
    _, or_mask, floats, addr, v = i
    generate_possible(floats, 0, addr | or_mask) do |addr|
      memory[addr] = v
    end
  end
  memory.values.sum
end

puts part1(input)
puts part2(input)
