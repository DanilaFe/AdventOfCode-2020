require "advent"
INPUT = input(2020, 18).lines

class Array(T)
  def push_op(op)
    r = pop
    l = pop
    self << ((op == '*') ? (l*r) : (l+r))
  end

  def has_op?
    !empty? && last != '('
  end
end

def translate(toks, prec)
  output = [] of Int64
  stack = [] of Char
  toks.each do |tok|
    case tok
    when .number? then output << tok.to_i64
    when '(' then stack << '('
    when ')'
      while stack.has_op?
        output.push_op(stack.pop)
      end
      stack.pop
    else
      while stack.has_op? && prec[stack.last] < prec[tok]
        output.push_op(stack.pop)
      end
      stack << tok
    end
  end
  while stack.has_op?
    output.push_op(stack.pop)
  end
  output.last
end

def part1(input)
  input.sum do |line|
    translate(line.chars.reject &.==(' '), {'*' => 0, '+' => 0})
  end
end

def part2(input)
  input.sum do |line|
    translate(line.chars.reject &.==(' '), {'*' => 1, '+' => 0})
  end
end

puts part1(INPUT.clone)
puts part2(INPUT.clone)
