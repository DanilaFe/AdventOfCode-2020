require "advent"
tiles = input(2020, 20).split "\n\n"
tiles.pop
thash = {} of Int32 => Array(Array(Char))
tiles = tiles.map do |t|
  tl = t.lines
  tid = tl[0].match(/Tile (\d+):/).not_nil![1].to_i32
  tls = tl[1..]
  thash[tid] = tls.map &.chars
end

class Array(T)
  def matches?(other)
    zip_with(other) { |l,r| l == r }.all?
  end

  def rotate
    reverse.transpose
  end
end

def check(side_a, side_b)
  return :normal if side_a.matches?(side_b)
  return :flip if side_a.matches?(side_b.reverse)
  return nil
end

def check_all(side_a, other, other_t)
  check(side_a, other.first) || check(side_a, other.last) || check(side_a, other_t.first) || check(side_a, other_t.last)
end

MONSTER = [ {0, 1}, {1, 0}, {4, 0}, {5, 1}, {6, 1}, {7, 0}, {10, 0}, {11,1}, {12, 1}, {13, 0}, {16, 0},
            {17, 1}, {18, 1}, {18, 2}, {19, 1} ]

def stitch(m, thash, corner)
  image = Array(Array(Char)).new(12*8) do |y|
    Array(Char).new(12*8) do |x|
      '.'
    end
  end

  tile = thash[corner]
  tile_id = corner
  tile.reverse! if m[corner].has_key? :top
  tile.each &.reverse! if m[corner].has_key? :left

  12.times do |row|
    tile = tile.not_nil!

    row_tile = tile
    row_id = tile_id

    12.times do |col|
      row_tile = row_tile.not_nil!

      (0..7).each do |y|
        (0..7).each do |x|
          image[col*8+y][row*8+x] = row_tile[y+1][x+1]
        end
      end

      matches = nil
      thash.each do |other_id, other_tile|
        next if matches
        next if other_id == row_id
        4.times do
          if row_tile.last.matches? other_tile.first
            row_id = other_id
            matches = other_tile
          elsif row_tile.last.matches? other_tile.first.reverse
            row_id = other_id
            matches = other_tile.map &.reverse
          end
          other_tile = other_tile.rotate
        end
      end

      row_tile = matches
    end

    rot = tile.rotate
    matches = nil
    thash.each do |other_id, other_tile|
      next if matches
      next if other_id == tile_id

      4.times do
        if rot.last.matches? other_tile.first
          tile_id = other_id
          matches = other_tile.rotate.rotate.rotate
        elsif rot.last.matches? other_tile.first.reverse
          tile_id = other_id
          matches = other_tile.map(&.reverse).rotate.rotate.rotate
        end
        other_tile = other_tile.rotate
      end
    end
    tile = matches
  end
  image
end

def find_dragons(stitch)
  dragons = [] of {Int32,Int32}
  stitch.each_with_index do |row, y|
    row.each_with_index do |c, x|
      is_dragon =  MONSTER.all? do |dx, dy|
        (stitch[y+dy]?.try &.[x+dx]?) == '#'
      end
      dragons << {x,y} if is_dragon
    end
  end
  dragons
end

def find_all_dragons(stitch)
  dragons = [] of {Int32,Int32}
  4.times do
    dragons.concat find_dragons(stitch)
    dragons.concat find_dragons(stitch.reverse)
    stitch = stitch.rotate
  end
  dragons
end

def match(thash, tile)
  matches = {} of Symbol => {Int32, Symbol}
  cs = thash[tile]
  tcs = cs.transpose

  thash.each do |t, ocs|
    next if t == tile
    tocs = ocs.transpose
    top = check_all(cs.first, ocs, tocs)
    bottom = check_all(cs.last, ocs, tocs)
    left = check_all(tcs.first, ocs, tocs)
    right = check_all(tcs.last, ocs, tocs)

    matches[:top]    = {t, top} if top
    matches[:left]   = {t, left} if left
    matches[:bottom] = {t, bottom} if bottom
    matches[:right]  = {t, right} if right
  end
  matches
end

def part1(input)
  corners = input.select do |t, i|
    match(input, t).size == 2
  end
  corners.keys.map(&.to_i64).product
end

def part2(input)
  matches = {} of Int32 => Hash(Symbol, {Int32, Symbol})
  corners = input.select do |t, i|
    matches[t] = match(input, t)
    match(input, t).size == 2
  end
  stitched = stitch(matches, input, corners.first[0])
  dragons = find_all_dragons(stitched)
  stitched.sum(&.count(&.==('#'))) - (dragons.size * MONSTER.size)
end

puts part1(thash.clone)
puts part2(thash.clone)
