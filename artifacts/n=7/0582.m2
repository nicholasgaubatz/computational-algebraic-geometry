                                                                                                                                        2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  )}
                              8 9    8 10    9 10   4 5    4 10    5 10   2 3    2 10    3 10   1 3    1 5    3 5   1 2    1 4    2 4   1   2   3   4   5   6   7   8   9   10
                                2    2         2   2   2   2         2   2               2         2
          AOTinIdeal => ideal (y  , y , y y , y , y , y , y , y y , y , y , y y , y y , y , y y , y )
                                10   9   8 9   8   7   6   5   4 5   4   3   2 3   1 3   2   1 2   1
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {5, 6}}
                                  2      3      4      5      6
          hSeries => 1 + 10T + 40T  + 82T  + 91T  + 52T  + 12T
          hyperplanes => {a - d, d - f, d - g, a - f, a - g, b - e, c - e, b - f, b - g, f - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_9-y_8*y_10+y_9*y_10, y_4*y_5-y_4*y_10+y_5*y_10, y_2*y_3-y_2*y_10+y_3*y_10, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {5, 6}}
