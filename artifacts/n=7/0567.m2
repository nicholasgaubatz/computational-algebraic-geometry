                                                                                                                                                                                      2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y   + y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  + y y y   - y y y   - y y y  , y , y , y , y , y , y , y , y , y , y  )}
                              8 9    8 10    9 10   6 7    6 10    7 10   4 5 7    4 5 9    4 7 9    5 7 9   4 5 6    4 5 8    4 6 8    5 6 8   1 2 3    1 2 10    1 3 10    2 3 10   1   2   3   4   5   6   7   8   9   10
                                2    2         2   2         2   2   2   2   2   2
          AOTinIdeal => ideal (y  , y , y y , y , y , y y , y , y , y , y , y , y , y y y , y y y , y y y )
                                10   9   8 9   8   7   6 7   6   5   4   3   2   1   4 5 7   4 5 6   1 2 3
          graph => {set {0, 3}, set {3, 6}, set {0, 5}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4      5      6
          hSeries => 1 + 10T + 43T  + 101T  + 136T  + 99T  + 30T
          hyperplanes => {a - d, d - g, a - f, b - e, c - e, b - f, b - g, c - f, c - g, f - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_9-y_8*y_10+y_9*y_10, y_6*y_7-y_6*y_10+y_7*y_10, y_4*y_5*y_7-y_4*y_5*y_9-y_4*y_7*y_9+y_5*y_7*y_9, y_4*y_5*y_6-y_4*y_5*y_8-y_4*y_6*y_8+y_5*y_6*y_8, y_1*y_2*y_3+y_1*y_2*y_10-y_1*y_3*y_10-y_2*y_3*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_4*y_5*y_7, y_4*y_5*y_6, y_1*y_2*y_3}})
G = graph {set {0, 3}, set {3, 6}, set {0, 5}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
