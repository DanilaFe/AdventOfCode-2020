INPUT = File.read("day4.txt").lines.map(&.chomp) 

def part1
  input = INPUT.clone
  passlines = [] of Array(String)
  currpass = [] of String
  input.each do |line|
    if line.empty?
      passlines << currpass
      currpass = [] of String
      next
    end
    currpass << line
  end
  passlines << currpass

  total = 0
  passlines.each do |pass|
    fields = pass.join(" ").split(" ")
    puts fields
    values = {} of String => String
    fields.each do |field|
      key = field.split(":")[0]
      values[key] = field.split(":")[1]
      puts "#{key}: #{values[key]}"
    end

    next unless value = values["byr"]?
    value = value.to_i32
    next unless value >= 1920 && value <= 2002

    puts "byr"

    next unless value = values["iyr"]?
    value = value.to_i32
    next unless value >= 2010 && value <= 2020
  
    puts "iry"

    next unless value = values["eyr"]?
    value = value.to_i32
    next unless value >= 2020 && value <= 2030

    puts "eyr"

    next unless value = values["hgt"]?
    next unless value.ends_with?("cm") || value.ends_with?("in")
    ivalue = value[0..-3].to_i32
    if value.ends_with? "cm"
      next unless ivalue >= 150 && ivalue <= 193
    else
      next unless ivalue >= 59 && ivalue <= 76
    end

    puts "hgt"

    next unless value = values["hcl"]?
    next unless value[0] == '#' && (value[1..]).to_i32(16)

    puts "hcl"

    next unless value = values["ecl"]?
    next unless "amb blu brn gry grn hzl oth".split(" ").includes? value

    puts "ecl"

    next unless value = values["pid"]?
    puts value
    next unless value.size == 9
    next unless value = value.to_i32?

    puts "pid"

    total += 1
  end
  puts total
end

def part2
  input = INPUT.clone
end

part1
part2
