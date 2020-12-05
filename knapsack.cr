class Array(T)
  def knapsack(budget, &cv : T -> {Int32,Int32})
    cost_values = map &cv

    memo = {} of {Int32, Int32} => Int32
    bt = {} of {Int32, Int32} => Bool
    compute = uninitialized Int32, Int32 -> Int32
    compute = ->(size : Int32, budget : Int32) {
      if m = memo[{size, budget}]?
        return m 
      end
      return memo[{size, budget}] = 0 if size == 0

      cost, value = cost_values[size-1]
      no_val = compute.call(size-1, budget)
      yes_val = (budget < cost) ? 0 : compute.call(size-1, budget - cost) + value  

      if yes_val > no_val
        bt[{size, budget}] = true
        return yes_val
      else
        bt[{size, budget}] = false
        return no_val
      end
    }

    value = compute.call(size, budget)
    i = size
    items = [] of T
    puts bt
    while i != 0
      if bt[{i, budget}]
        items << self[i-1]
        budget -= cost_values[i-1][0]
      end
      i -= 1
    end
    {value, items}
  end
end
