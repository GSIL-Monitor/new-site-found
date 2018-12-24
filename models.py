# coding: utf-8
from sqlalchemy import Column, DateTime, Integer, String, text, Text, Date, Index, Float
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.dialects.mysql import MEDIUMTEXT

Base = declarative_base()
metadata = Base.metadata


class BulletinList(Base):
    __tablename__ = 'bulletin_list'

    record_pk = Column(Integer, primary_key=True)
    location = Column(String(255))
    title = Column(String(255), nullable=False)
    url = Column(String(255), nullable=False, unique=True)
    release_data = Column(String(40))
    op_time = Column(DateTime, nullable=False)
    status = Column(Integer, nullable=False, index=True, server_default=text("'0'"))
    fields = Column(String(50))
    source = Column(String(100))
    simhash = Column(String(40))
    info_type = Column(String(50))
    plat_source = Column(String(100))
    business_source = Column(String(100))
    origin_url = Column(String(250))
    raw = Column(MEDIUMTEXT)

class BulletinQianlimaList(Base):
    __tablename__ = 'bulletin_qianlima_list'

    record_pk = Column(Integer, primary_key=True)
    location = Column(String(255))
    title = Column(String(255), nullable=False)
    url = Column(String(255), nullable=False, unique=True)
    release_data = Column(String(40))
    op_time = Column(DateTime, nullable=False)
    status = Column(Integer, nullable=False, index=True, server_default=text("'0'"))
    fields = Column(String(50))
    source = Column(String(100))
    simhash = Column(String(40))


class BulletinSearchDomainResult(Base):
    __tablename__ = 'bulletin_search_domain_result'

    record_pk = Column(Integer, primary_key=True)
    title = Column(String(255), nullable=False)
    domain = Column(String(255))
    op_time = Column(DateTime, nullable=False)
    status = Column(Integer, nullable=False, index=True, server_default=text("'0'"))
    sim = Column(Float)
    rate = Column(Float)
    ip_host = Column(String(255))
    port = Column(String(255))


class BulletinSearchList(Base):
    __tablename__ = 'bulletin_search_list'
    __table_args__ = (
        Index('idx_index', 'url', 'title', unique=True),
    )

    record_pk = Column(Integer, primary_key=True)
    location = Column(String(255))
    title = Column(String(255), nullable=False)
    url = Column(String(255))
    release_data = Column(Date)
    op_time = Column(DateTime, nullable=False)
    status = Column(Integer, nullable=False, index=True, server_default=text("'0'"))
    fields = Column(String(50))
    source = Column(String(100), index=True)
    simhash = Column(String(40), index=True, server_default=text("'0'"))
    info_type = Column(String(50), server_default=text("''"))
    plat_source = Column(String(100), index=True)
    business_source = Column(String(100))
    origin_url = Column(String(255))
    raw = Column(String)
    project_id = Column(String(200))


class BulletinSearchResult(Base):
    __tablename__ = 'bulletin_search_result'

    record_pk = Column(Integer, primary_key=True)
    location = Column(String(255))
    title = Column(String(255), nullable=False)
    url = Column(String(255))
    release_data = Column(Date)
    op_time = Column(DateTime, nullable=False)
    status = Column(Integer, nullable=False, index=True, server_default=text("'0'"))
    fields = Column(String(50))
    source = Column(String(100))
    simhash = Column(String(40), server_default=text("'0'"))
    info_type = Column(String(50), server_default=text("''"))
    plat_source = Column(String(100))
    business_source = Column(String(100))
    origin_url = Column(String(255))
    domain = Column(String(255), nullable=False)
    raw = Column(String)
    project_id = Column(String(200))
    level = Column(Integer)
    abstrac = Column(Text)
    pk = Column(Integer)
    simple_title = Column(String(255))
    keyword = Column(String(255))

