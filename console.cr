def parse(input)
  input.lines.map do |s|
    code, int = s.split(" ")
    {code, int.to_i32}
  end
end

def run(prog)
  acc = 0
  pc = 0
  visited = Set(Int32).new
  input = Channel(Int32).new
  output = Channel({Symbol, Int32}).new
  spawn do
    loop do
      if pc >= prog.size
        output.send({:term, acc})
        break
      elsif visited.includes? pc
        output.send({:inf, acc})
        break
      end

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
  {input, output}
end
