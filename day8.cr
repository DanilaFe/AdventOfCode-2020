require "advent"
INPUT = input(2020, 8).lines

def part1
  acc = 0
  pc = 0
  visited = Set(Int32).new
  input = INPUT.clone.map do |s|
    code, int = s.split(" ")
    {code, int.to_i32}
  end

  loop do
    if visited.includes? pc
      break
    end
    visited << pc
    code, int = input[pc]
    case input[pc][0]
    when "acc"
      acc += int
      pc += 1
    when "jmp"
      pc += int
    when "nop"
      pc += 1
    end
  end
end

def run(prog)
  acc = 0
  pc = 0
  visited = Set(Int32).new
  loop do
    if visited.includes? pc
      return false
    end
    return acc if pc >= prog.size
    visited << pc
    code, int = prog[pc]
    case prog[pc][0]
    when "acc"
      acc += int
      pc += 1
    when "jmp"
      pc += int
    when "nop"
      pc += 1
    end
  end
end

def part2
  input = INPUT.clone.map do |s|
    code, int = s.split(" ")
    {code, int.to_i32}
  end

  jnp = [] of Int32
  input.each_with_index do |e, i|
    op, int = e
    jnp << i if op == "jmp" || op == "nop"
  end

  jnp.each do |i|
    prog = input.clone
    if prog[i][0] == "jmp"
      prog[i] = {"nop", prog[i][1]}
    else
      prog[i] = {"jmp", prog[i][1]}
    end

    case i = run(prog)
    when Bool
      next
    when Int32
      return i
    end
  end
end

puts part1
puts part2
