require "advent"
require "./console.cr"

INPUT = input(2020, 8)

def part1
  run(parse(INPUT))[1].receive[1]
end

def part2
  input = parse(INPUT)
  jnp = input.find_indices { |e| e[0] == "jmp" || e[0] == "nop" }
  jnp.each do |i|
    prog = input.clone
    op, int = prog[i]
    prog[i] = {op.tr("jmpnop", "nopjmp"), int}

    code, acc = run(prog)[1].receive
    return acc if code == :term
  end
end

puts part1
puts part2
