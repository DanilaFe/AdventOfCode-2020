INPUT = File.read("day1.txt").lines.map(&.chomp.to_i32) 

def part1
  input = INPUT.clone
  input.each_with_index do |v, i|
    input.each_with_index do |v2, j|
      next unless v + v2 == 2020 && i != j
      puts v*v2
    end
  end
end

def part2
  input = INPUT.clone
  input.each_with_index do |v, i|
    input.each_with_index do |v2, j|
      next if j == i
      input.each_with_index do |v3, k|
        next if k == j || k == i
        puts v3*v2*v if v3 + v2 + v == 2020
      end
    end
  end
end

part1
part2
