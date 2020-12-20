require "advent"

rlines, _, strings = input(2020, 19).partition("\n\n")
strings = strings.lines
rules = {} of String => String
rlines.lines.map do |l|
  rule, _, text = l.partition(": ")
  rules[rule] = text
end

alias Matcher = Proc(String,Int32,Array(Int32))

def char(c)
  ->(str : String, i : Int32) { str[i]? == c ? [i+1] : [] of Int32 }
end

def any(ps)
  ->(str : String, i : Int32) { ps.flat_map { |p| p.call(str, i) } }
end

def seq(ps)
  ->(str : String, i : Int32) {
    base = [i]
    ps.each do |p|
      base = base.flat_map { |i| p.call(str, i) }
    end
    base
  }
end

def to_regex(rules, rule)
end

def build_rule(rules, built, rule) : Matcher
  if exists = built[rule]?
    return exists 
  end

  body = rules[rule]
  return built[rule] = char body[1] if body.matches? /"."/
  
  branches = [] of Matcher
  top = any(branches)
  built[rule] = top
  branches.concat(body.split(" | ").map { |b| seq(b.split(" ").map { |subrule| build_rule(rules, built, subrule) }) })
  top
end

def part1(input)
  rules, lines = input
  matcher = build_rule(rules, {} of String => Matcher, "0")
  lines.count do |l|
    matcher.call(l, 0).includes? l.size
  end
end

def part2(input)
  rules, lines = input
  rules["8"] = "42 | 42 8"
  rules["11"] = "42 31 | 42 11 31"
  matcher = build_rule(rules, {} of String => Matcher, "0")
  lines.count do |l|
    matcher.call(l, 0).includes? l.size
  end
end

puts part1({rules,strings})
puts part2({rules,strings})
