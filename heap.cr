class Array(T)
  def bubble_up(i, &cmp)
    return if i >= size
    while i != 0
      j = (i-1)//2
      break if yield self[i], self[j]
      self[i], self[j] = self[j], self[i]
      i = j
    end
  end

  def percalate_down(i, &cmp)
    while i*2+1 < size
      j1, j2 = i*2+1, i*2+2
      v1 = self[j1]
      v2 = self[j2]?
      if v2 && (yield v1, v2) && (yield self[i], v2)
        self[j2], self[i] = self[i], v2
        i = j2
      elsif yield self[i], v1
        self[j1], self[i] = self[i], v1
        i = j1
      else
        break
      end
    end
  end

  def heapify(&cmp : T,T -> Bool)
    size.times do |i|
      i = size - i - 1
      bubble_up(i, &cmp)
    end
    self
  end

  def heapify
    heapify do |i,j|
      i < j
    end
  end

  def heap_push(v, &cmp : T,T -> Bool)
    self << v
    bubble_up(size - 1, &cmp)
  end

  def heap_push(v)
    heap_push(v) do |i,j|
      i < j
    end
  end

  def heap_pop(&cmp : T,T -> Bool)
    self[0], self[size-1] = self[size-1], self[0]
    v = pop
    percalate_down(0, &cmp)
    v
  end

  def heap_pop
    heap_pop do |i, j|
      i < j
    end
  end

  def is_heap?(&cmp : T,T -> Bool)
    (size-1).times do |i|
      i = size - i - 1
      vi = self[i]
      vp = self[(i-1)//2]
      return false unless (yield self[i], self[(i-1)//2]) || vi == vp
    end
    return true
  end

  def is_heap?
    is_heap? do |i,j|
      i < j
    end
  end

end
