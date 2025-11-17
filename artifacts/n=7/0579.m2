                                                                                                                               2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              6 7    6 10    7 10   5 7    5 9    7 9   1 2    1 3    2 3   3 4 8    3 4 9    3 8 9    4 8 9   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2               2   2   2   2   2         2
          AOTinIdeal => ideal (y  , y , y , y , y y , y y , y , y , y , y , y , y y , y , y y y , y y y )
                                10   9   8   7   6 7   5 7   6   5   4   3   2   1 2   1   5 6 9   3 4 8
          graph => {set {0, 3}, set {3, 5}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 42T  + 95T  + 122T  + 84T  + 24T
          hyperplanes => {a - d, d - f, a - f, a - g, b - e, c - e, e - g, b - f, b - g, c - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_10-y_7*y_10, y_5*y_7-y_5*y_9-y_7*y_9, y_1*y_2-y_1*y_3-y_2*y_3, y_3*y_4*y_8-y_3*y_4*y_9-y_3*y_8*y_9+y_4*y_8*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_9, y_3*y_4*y_8}})
G = graph {set {0, 3}, set {3, 5}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}}
