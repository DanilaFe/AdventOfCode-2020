INPUT = File.read("day4.txt").lines.map(&.chomp) 

def parse_passport(string)
  new_hash = {} of String => String
  string.split(" ").each do |field|
    k,v = field.split(":")
    new_hash[k] = v
  end
  new_hash
end

def parse_passports(lines)
  passports = [] of Hash(String, String)
  passport = [] of String

  lines.each do |line|
    unless line.empty?
      passport << line
      next
    end

    passports << parse_passport(passport.join(" "))
    passport = [] of String
  end
  passports << parse_passport(passport.join(" "))
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

def part2
  input = INPUT.clone
  passports = parse_passports(input)
  total = passports.count do |passport|
    next unless value = passport["byr"]?
    value = value.to_i32
    next unless value >= 1920 && value <= 2002

    next unless value = passport["iyr"]?
    value = value.to_i32
    next unless value >= 2010 && value <= 2020
  
    next unless value = passport["eyr"]?
    value = value.to_i32
    next unless value >= 2020 && value <= 2030

    next unless value = passport["hgt"]?
    next unless value.ends_with?("cm") || value.ends_with?("in")
    ivalue = value[0..-3].to_i32
    if value.ends_with? "cm"
      next unless ivalue >= 150 && ivalue <= 193
    else
      next unless ivalue >= 59 && ivalue <= 76
    end

    next unless value = passport["hcl"]?
    next unless value[0] == '#' && (value[1..]).to_i32(16)

    next unless value = passport["ecl"]?
    next unless "amb blu brn gry grn hzl oth".split(" ").includes? value

    next unless value = passport["pid"]?
    next unless value.size == 9
    next unless value = value.to_i32?
  
    true
  end
  puts total
end

part1
part2
