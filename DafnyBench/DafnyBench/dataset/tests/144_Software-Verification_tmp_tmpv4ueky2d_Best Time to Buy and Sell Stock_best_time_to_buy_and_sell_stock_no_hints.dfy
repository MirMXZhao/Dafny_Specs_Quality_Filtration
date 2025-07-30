method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{}

////////TESTS////////

method testbest_time_to_buy_and_sell_stock1() {
  var prices := new int[6] [7, 1, 5, 3, 6, 4];
  var max_profit := best_time_to_buy_and_sell_stock(prices);
  assert max_profit == 5;
}

method testbest_time_to_buy_and_sell_stock2() {
  var prices := new int[5] [7, 6, 4, 3, 1];
  var max_profit := best_time_to_buy_and_sell_stock(prices);
  assert max_profit == 0;
}

method testbest_time_to_buy_and_sell_stock3() {
  var prices := new int[1] [5];
  var max_profit := best_time_to_buy_and_sell_stock(prices);
  assert max_profit == 0;
}
