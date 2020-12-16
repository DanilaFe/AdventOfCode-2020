require "advent"

def parse_range(str)
  data = str.match(/([a-z ]+): (\d+)-(\d+) or (\d+)-(\d+)/).not_nil!
  return {data[1], (data[2].to_i32..data[3].to_i32), (data[4].to_i32.. data[5].to_i32)}
end

fields, your, nearby = input(2020, 16).split("\n\n")
fields = fields.lines.map { |l| parse_range(l) }
your = your.lines[1].split(",").map(&.to_i32)
nearby = nearby.lines[1..].map(&.split(",").map(&.to_i32))

def part1(input)
  fields, your, nearby = input
  all_ranges = [] of Range(Int32, Int32)
  fields.each do |a|
    all_ranges << a[1] << a[2]
  end
  nearby.select! do |nb|
    nb.all? do |n|
      all_ranges.any? &.includes?(n)
    end
  end
  nearby << your
  field_map = {} of String => Set(Int32)
  fields.each do |f|
    field_map[f[0]] = Set(Int32).new
    nearby[0].size.times do |i|
      next if field_map.values.includes? i
      all_match = nearby.all? do |nb|
        f[1].includes?(nb[i]) || f[2].includes?(nb[i])
      end
      if all_match
        field_map[f[0]] << i
      end
    end
  end
  sum = 1_u64
  numbers = (0...nearby[0].size).to_a
  solved = {} of String => Int32
  while solved.size != fields.size
    cleared = [] of {String, Int32}
    field_map.each do |k, v|
      next unless v.size == 1
      cleared << {k, v.to_a[0]}
    end
    cleared.each do |f,n|
      solved[f] = n
      field_map.each do |k, v|
        v.delete n
      end
    end
  end
  fields.each do |f|
    next unless f[0].starts_with? "departure"
    sum *= your[solved[f[0]]]
  end
  sum
end

def part2(input)
end

puts part1({fields, your, nearby})
puts part2({fields, your, nearby})
