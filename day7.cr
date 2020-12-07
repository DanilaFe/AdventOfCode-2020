require "advent"

INPUT = input(2020, 7).lines.map(&.chomp).map do |s|
  data = s.match(/^([a-z ]+) bags contain (.*).$/).not_nil!
  {data[1], data[2].split(", ").map(&.rchop(" bags").rchop(" bag")) }
end

def build_graph(input)
  gr = Graph(String).new
  seen = Set(String).new
  input.each do |i|
    next if i[1] == ["no other"]
    seen << i[0]
    i[1].each do |to|
      n, _, m = to.partition(" ")
      n = n.to_i32
      gr.add_edge(i[0], m, n)
    end
  end
  {seen, gr}
end

def part1
  seen, gr = build_graph(INPUT)
  seen.count do |s|
    gr.find_path(s, "shiny gold") && s != "shiny gold"
  end
end

def count_bags(gr, current)
  return 1 unless es = gr.@edges[current]?
  1 + es.sum do |e|
    t, k = e
    k * count_bags(gr, t)
  end
end

def part2
  seen, gr = build_graph(INPUT)
  count_bags(gr, "shiny gold") - 1
end

puts part1
puts part2
