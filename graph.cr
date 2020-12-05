class Graph(A)
  def initialize
    @edges = {} of A => Set({A, Int32})
  end

  def add_edge(f, t, c = 1)
    @edges[f] ||= Set({A, Int32}).new
    @edges[f] << {t, c}
  end

  def add_biedge(f, t, c = 1)
    add_edge(f, t, c)
    add_edge(t, f, c)
  end

  def find_path(f, t)
    visited = Set(A).new
    candidates = Set { f }
    distances = {f => 0}
    prev = {} of A => A

    while !candidates.empty?
      candidate = candidates.min_by { |c| distances[c] }
      break if candidate == t
      visited << candidate
      candidates.delete candidate
      dist = distances[candidate]

      @edges.fetch(candidate, Set({A, Int32}).new).each do |e|
        node, cost = e
        new_dist = dist + cost
        candidates << node unless visited.includes? node
        next if (old_dist = distances[node]?) && old_dist < new_dist
        distances[node] = new_dist 
        prev[node] = candidate
      end
    end

    backtrack = t
    path = [t] of A
    while backtrack != f
      return nil unless prev_bt = prev[backtrack]?
      path << prev_bt
      backtrack = prev_bt
    end
    {path.reverse!, distances[t]}
  end
end
