require "advent"
input = input(2020, 21).lines.map do |line|
  data = line.match(/^([a-z ]+) \(contains (.+)\)$/).not_nil!
  {data[1].split(" ").to_set, data[2].split(", ").to_set}
end

allergens = input.flat_map(&.last.to_a).to_set
ingredients = input.flat_map(&.first.to_a).to_set

allergen_sets = {} of String => Set(String)
allergens.each do |a|
  input.each do |ings, als|
    next unless als.includes? a
    allergen_sets[a] ||= ings
    allergen_sets[a] &= ings
  end
end

safe = ingredients.reject { |i| allergen_sets.any? &.last.includes?(i) }
puts "Part 1: #{input.sum &.first.count { |i| safe.includes? i }}"

known_allergens = {} of String => String
while allergen_sets.size > known_allergens.size
  allergen_sets.each do |a, s|
    next unless s.size == 1
    new_known = s.first
    known_allergens[a] = new_known
    allergen_sets.each &.last.delete(new_known)
  end
end
puts "Part 2: #{known_allergens.to_a.sort_by(&.first).map(&.last).join(",")}"
