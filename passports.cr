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

class Validator(T, R)
  def initialize(@proc : Proc(T, R?))
  end

  def >>(other)
    Validator.new(->(i : T) { @proc.call(i).try { |j| other.@proc.call(j) } })
  end

  def then(&block : R -> S?) forall S
    Validator(T, S).new(->(i : T) { @proc.call(i).try { |j| block.call(j) } })
  end

  def run(input)
    @proc.call(input)
  end
end

class Hash(K,V)
  def validate(k, vl)
    self[k]?.try { |v| vl.run(v) }
  end
end

def range(range) : Validator(Int32, Int32)
  Validator.new ->(i : Int32) { (range.includes? i) ? i : nil }
end

def int : Validator(String, Int32)
  Validator.new ->(s : String) { s.to_i32? }
end

def regex(regex) : Validator(String, Regex::MatchData)
  Validator(String, Regex::MatchData).new ->(s : String) { s.match(regex) }
end

def oneof(strs : Array(A)) : Validator(A, A) forall A
  Validator(String, String).new ->(s : String) { (strs.includes? s) ? s : nil }
end

def length(len) : Validator(String, String)
  Validator(String, String).new ->(s : String) { (s.size == len) ? s : nil }
end

def year(rng) : Validator(String, Int32)
  length(4) >> int >> range(rng)
end

def unit_range(map) : Validator(String, {String, Int32})
  regex(/(\d+)([a-zA-Z]+)/).then do |md|
    map[md[2]]?.try { |r| (int >> range(r)).run(md[1]).try { |i| {md[2], i} } }
  end
end

class Passport
  def initialize(
    @byr : Int32, @iyr : Int32,
    @eyr : Int32, @hgt : {String, Int32},
    @hcl : String, @ecl : String, @pid : Int32)
  end

  def self.from_hash?(hash)
    return nil unless byr = hash.validate("byr", year(1920..2002))
    return nil unless iyr = hash.validate("iyr", year(2010..2020))
    return nil unless eyr = hash.validate("eyr", year(2020..2030))
    return nil unless hgt = hash.validate("hgt", unit_range({"cm" => (150..193), "in" => (59..76)}))
    return nil unless hcl = hash.validate("hcl", regex(/^#([0-9a-f]{6})$/).then { |d| d[1] })
    return nil unless ecl = hash.validate("ecl", oneof(["amb", "blu", "brn", "gry", "grn", "hzl", "oth"]))
    return nil unless pid = hash.validate("pid", length(9) >> int)
    Passport.new(byr, iyr, eyr, hgt, hcl, ecl, pid)
  end
end
