require "./passports.cr"
INPUT = File.read("day4.txt")

def part1
  input = INPUT.clone
  passports = parse_passports(input)
  total = passports.count do |passport|
    ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"].all? do |key|
      passport.has_key? key
    end
  end
  puts total
end

def part2
  input = INPUT.clone
  passports = parse_passports(input)
  total = passports.count do |passport|
    DEFAULT_VALIDATORS.all? do |k, v|
      passport[k]?.try { |s| v.call(s) }
    end
  end
  puts total
end

part1
part2
