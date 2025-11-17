                                                                                                                2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  )}
                              7 8    7 10    8 10   6 8    6 9    8 9   2 3    2 5    3 5   1 3    1 4    3 4   1   2   3   4   5   6   7   8   9   10
                                2    2   2               2   2   2   2   2               2   2
          AOTinIdeal => ideal (y  , y , y , y y , y y , y , y , y , y , y , y y , y y , y , y , y y y , y y y )
                                10   9   8   7 8   6 8   7   6   5   4   3   2 3   1 3   2   1   6 7 9   1 2 4
          graph => {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 6}, set {1, 6}, set {2, 5}, set {3, 5}, set {5, 6}, set {2, 6}, set {3, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 41T  + 88T  + 104T  + 64T  + 16T
          hyperplanes => {a - e, b - e, e - g, a - g, b - g, c - f, d - f, f - g, c - g, d - g}
          numVariables => 10
          WLPfull => "A does not have WLP at A_3"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_10-y_8*y_10, y_6*y_8-y_6*y_9-y_8*y_9, y_2*y_3-y_2*y_5-y_3*y_5, y_1*y_3-y_1*y_4-y_3*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}},{{y_10^2, y_9^2, y_8^2, y_7*y_8, y_6*y_8, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_6*y_7*y_9, y_1*y_2*y_4}})
G = graph {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 6}, set {1, 6}, set {2, 5}, set {3, 5}, set {5, 6}, set {2, 6}, set {3, 6}}
