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
  valid_passports = [] of Passport
  passports.each do |p|
    if vp = Passport.from_hash?(p)
      valid_passports << vp 
    end
  end
  puts valid_passports.size
end

part1
part2
