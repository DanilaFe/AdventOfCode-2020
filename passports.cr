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

def validate_range(range)
  ->(s : String) { s.to_i32?.try { |i| range.includes? i } }
end

def validate_regex(regex)
  ->(s : String) { s.matches?(regex) }
end

def validate_unit_range(unit_ranges)
  ->(s : String) {
    return false unless s.match(/^(\d+)([a-zA-Z]+)$/)
    unit_ranges[$~[2]]?.try { |rng| validate_range(rng).call($~[1]) }
  }
end

DEFAULT_VALIDATORS = {
  "byr" => validate_range(1920..2002),
  "iyr" => validate_range(2010..2020),
  "eyr" => validate_range(2020..2030),
  "hgt" => validate_unit_range({"cm" => (150..193), "in" => (59..76)}),
  "hcl" => validate_regex(/^#[0-9a-f]{6}$/),
  "ecl" => ->(s : String) { "amb blu brn gry grn hzl oth".split(" ").includes? s },
  "pid" => ->(s : String) { s =~ /^[0-9]{9}$/ },
}
