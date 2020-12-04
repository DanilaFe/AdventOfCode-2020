INPUT = File.read("day4.txt")

def parse_passport(string)
  new_hash = {} of String => String
  string.split(" ").each do |field|
    k,v = field.split(":")
    new_hash[k] = v
  end
  new_hash
end

def parse_passports(lines)
  lines.split(/\n\n/).map do |s|
    parse_passport(s.chomp.gsub(/\n/, " "))
  end
end

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

def validate_range(range)
  ->(s : String) { s.to_i32?.try { |i| range.includes? i } }
end

def validate_regex(regex)
  ->(s : String) { s.matches?(regex) }
end

def part2
  input = INPUT.clone
  passports = parse_passports(input)
  validators = {
    "byr" => validate_range(1920..2002),
    "iyr" => validate_range(2010..2020),
    "eyr" => validate_range(2020..2030),
    "hgt" => ->(s : String) {
      return false unless s.match(/^(\d+)(cm|in)$/)
      validate_range($~[2] == "cm" ? (150..193) : (59..76)).call($~[1])
    },
    "hcl" => validate_regex(/^#[0-9a-f]{6}$/),
    "ecl" => ->(s : String) { "amb blu brn gry grn hzl oth".split(" ").includes? s },
    "pid" => ->(s : String) { s =~ /^[0-9]{9}$/ },
  }
  total = passports.count do |passport|
    validators.all? do |k, v|
      passport[k]?.try { |s| v.call(s) }
    end
  end
  puts total
end

part1
part2
