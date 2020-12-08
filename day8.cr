require "advent"
INPUT = input(2020, 8).lines.map do |s|
  code, int = s.split(" ")
  {code, int.to_i32}
end

def run(prog)
  acc = 0
  pc = 0
  visited = Set(Int32).new
  loop do
    return {:term, acc} if pc >= prog.size
    return {:inf, acc} if visited.includes? pc
      
    visited << pc
    code, int = prog[pc]
    case code
    when "acc"
      acc += int
    when "jmp"
      pc += int - 1
    end
    pc += 1
  end
end

def part1
  run(INPUT)[1]
end

def part2
  jnp = INPUT.find_indices { |e| e[0] == "jmp" || e[0] == "nop" }
  jnp.each do |i|
    prog = INPUT.clone
    op, int = prog[i]
    prog[i] = {op.tr("jmpnop", "nopjmp"), int}

    code, acc = run(prog)
    return acc if code == :term
  end
end

puts part1
puts part2
