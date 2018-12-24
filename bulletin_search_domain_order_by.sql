-- 创建临时表 通过聚合ip_host  生成排序字段 用完之后删除
CREATE TABLE
IF NOT EXISTS `bulletin_search_tmp_order_by` (
	`record_pk` INT (11) NOT NULL AUTO_INCREMENT,
	`ip_host` VARCHAR (20) DEFAULT NULL,
	`order_by` FLOAT DEFAULT '0' COMMENT '排序字段',
	PRIMARY KEY (`record_pk`)
) ENGINE = INNODB AUTO_INCREMENT = 1 DEFAULT CHARSET = utf8 ROW_FORMAT = COMPRESSED COMMENT = ' ';

INSERT IGNORE INTO bulletin_search_tmp_order_by (ip_host, order_by) SELECT
	ip_host,
	sum(rate)
FROM
	bulletin_search_domain_result
WHERE
	ip_host > ''
GROUP BY
	ip_host;

UPDATE bulletin_search_tmp_order_by o,
 bulletin_search_domain_result b
SET b.order_by = o.order_by
WHERE
	o.ip_host = b.ip_host;

DROP TABLE `bulletin_search_tmp_order_by`;

-- 更新ip_host标识为商业站点但是未识别出来的域名
UPDATE bulletin_search_domain_result r1,
 bulletin_search_domain_result r2
SET r1.business = 1
WHERE
	r1.business = 0
AND r2.business = 1
AND r1.ip_host > ''
AND r1.ip_host = r2.ip_host;