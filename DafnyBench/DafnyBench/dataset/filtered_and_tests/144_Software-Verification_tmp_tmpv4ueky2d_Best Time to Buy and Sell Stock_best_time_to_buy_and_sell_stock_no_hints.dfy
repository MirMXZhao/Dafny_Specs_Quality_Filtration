method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{}



method TestBestTimeToBuyAndSellStock1() {
  var prices := new int[4];
  prices[0] := 7;
  prices[1] := 1;
  prices[2] := 5;
  prices[3] := 3;
  var max_profit := best_time_to_buy_and_sell_stock(prices);
  assert max_profit == 4;
}

method TestBestTimeToBuyAndSellStock2() {
  var prices := new int[3];
  prices[0] := 5;
  prices[1] := 4;
  prices[2] := 3;
  var max_profit := best_time_to_buy_and_sell_stock(prices);
  assert max_profit == 0;
}
