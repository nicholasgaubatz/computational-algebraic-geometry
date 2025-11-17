                                                                      2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y )}
                              2 3    2 5    3 5   1 3    1 4    3 4   1   2   3   4   5
                                2   2   2               2   2
          AOTinIdeal => ideal (y , y , y , y y , y y , y , y , y y y )
                                5   4   3   2 3   1 3   2   1   1 2 4
          graph => {set {0, 2}, set {1, 2}, set {2, 3}, set {0, 3}, set {1, 3}}
                                2     3
          hSeries => 1 + 5T + 8T  + 4T
          hyperplanes => {a - c, b - c, c - d, a - d, b - d}
          numVariables => 5
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_5]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_2*y_3-y_2*y_5-y_3*y_5, y_1*y_3-y_1*y_4-y_3*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_1*y_2*y_4}})
G = graph {set {0, 2}, set {1, 2}, set {2, 3}, set {0, 3}, set {1, 3}}
