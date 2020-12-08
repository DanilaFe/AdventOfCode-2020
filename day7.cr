require "advent"

INPUT = input(2020, 7).lines.map(&.chomp).map do |s|
  data = s.match(/^([a-z ]+) bags contain (.*).$/).not_nil!
  contents = data[2].split(", ").compact_map do |s|
    s.match(/(\d+) (.*) bags?/).try { |m| {m[1].to_i32, m[2]} }
  end
  {data[1], contents}
end

def build_graph(input)
  gr = Graph(String).new
  seen = Set(String).new
  input.each do |i|
    seen << i[0]
    i[1].each do |to|
      n, m = to
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
