//! Parsing and applying robots.txt files.
//!
//! # Examples
//! ```
//! use roboto::Robots;
//!
//! let robots = r#"
//! User-agent: *
//! Disallow: /
//! "#.parse::<Robots>().unwrap();
//!
//! assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/"));
//! assert!(robots.is_allowed(&"googlebot".parse().unwrap(), "/robots.txt"));
//! assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/foo/bar"));
//! ```
//!
//! # References
//! - [The Web Robots Pages](https://www.robotstxt.org/)
//! - [RFC1945](https://datatracker.ietf.org/doc/html/rfc1945#section-3.7)
//! - [WikiPedia](https://en.wikipedia.org/wiki/Robots_exclusion_standard)
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![deny(unsafe_code)]

use std::{fmt, hash::Hash, ops::Deref, str::FromStr};

use camino::Utf8Path;

pub mod error;
use crate::error::DirectiveParseError;
use crate::error::DirectivePathParseError;
use crate::error::RobotParseError;
use crate::error::UserAgentParseError;

const TSPECIALS: &str = "()<>@,;:\\\"/[]?={} \t";
const PSAFE: &str = "$-_.+~";
const PEXTRA: &str = "!*'(),";

fn is_rfc1945_token(c: char) -> bool {
    c.is_ascii() && !c.is_ascii_control() || TSPECIALS.contains(c)
}
fn is_rfc1945_path(c: char) -> bool {
    c == '/' || c == '%' || c.is_ascii_alphanumeric() || PSAFE.contains(c) || PEXTRA.contains(c)
}

/// A User-Agent string.
///
/// This type represents a User-Agent string as defined in the [RFC1945](https://datatracker.ietf.org/doc/html/rfc1945#section-3.7).
///
/// # Examples
///
/// ```
/// use roboto::UserAgent;
///
/// let agent = "googlebot".parse::<UserAgent>().unwrap();
/// assert_eq!(agent.to_string(), "googlebot");
///
/// let agent = "*".parse::<UserAgent>().unwrap();
/// assert_eq!(agent, UserAgent::ANY);
///
/// // User agents must be valid ascii
/// assert!("😀".parse::<UserAgent>().is_err());
/// ```
#[derive(Debug, Clone)]
pub struct UserAgent(Option<Box<str>>);

impl UserAgent {
    /// A User-Agent string that matches all User-Agents.
    ///
    /// This is normally spelled as `*` in a robots.txt file.
    pub const ANY: UserAgent = UserAgent(None);

    fn is_wildcard(&self) -> bool {
        self.0.is_none()
    }
}

impl PartialEq for UserAgent {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => a == b,
            (None, _) => true,
            (_, None) => true,
        }
    }
}

impl Eq for UserAgent {}

impl Hash for UserAgent {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.0 {
            Some(agent) => agent.hash(state),
            None => "*".hash(state),
        }
    }
}

impl FromStr for UserAgent {
    type Err = UserAgentParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "*" {
            return Ok(UserAgent(None));
        }

        if s.is_empty() {
            return Err(UserAgentParseError::EmptyUserAgent);
        }

        if !s.is_ascii() {
            return Err(UserAgentParseError::InvalidUserAgentEncoding);
        }

        if !s.chars().all(is_rfc1945_token) {
            return Err(UserAgentParseError::InvalidCharacters);
        }

        Ok(UserAgent(Some(s.into())))
    }
}

impl fmt::Display for UserAgent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Some(agent) => write!(f, "{}", agent),
            None => write!(f, "*"),
        }
    }
}

#[derive(Debug, Clone, Hash)]
enum PathInner {
    None,
    Any,
    Path(Box<Utf8Path>),
    Robots,
}

/// A path directive in a robots.txt file.
///
/// Path directives can match any url path, spelled as `/, no path (left empty) or a specific path.
///
/// # Examples
/// ```
/// use roboto::DirectivePath;
///
/// let path = "/foo/bar".parse::<DirectivePath>().unwrap();
/// assert!(path.matches("/foo/bar/baz"));
///
/// let path = DirectivePath::ANY;
/// assert!(path.matches("/foo/bar/baz"));
///
/// let path = DirectivePath::NONE;
/// assert!(!path.matches("/foo/bar/baz"));
/// ````
#[derive(Debug, Clone)]
pub struct DirectivePath(PathInner);

impl DirectivePath {
    /// A directive path which matches all possible paths.
    pub const ANY: DirectivePath = DirectivePath(PathInner::Any);

    /// A directive path which matches no paths
    pub const NONE: DirectivePath = DirectivePath(PathInner::None);

    /// Matches just `/robots.txt`
    pub const ROBOTS: DirectivePath = DirectivePath(PathInner::Robots);

    /// Check if a path matches this directive path.
    pub fn matches(&self, path: &str) -> bool {
        match &self.0 {
            PathInner::None => false,
            PathInner::Any => true,
            PathInner::Path(pattern) => {
                let path = Utf8Path::new(path);
                path.starts_with(pattern.deref())
            }
            PathInner::Robots => {
                let path = Utf8Path::new(path);
                path == Utf8Path::new("/robots.txt")
            }
        }
    }

    /// Check if this directive path will match no paths.
    pub fn is_none(&self) -> bool {
        matches!(self.0, PathInner::None)
    }

    /// Check if this directive path will match any path.
    pub fn is_any(&self) -> bool {
        matches!(self.0, PathInner::Any)
    }

    /// Check if this directive path will match `/robots.txt`
    pub fn is_robots(&self) -> bool {
        matches!(self.0, PathInner::Robots)
    }
}

impl fmt::Display for DirectivePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            PathInner::None => write!(f, ""),
            PathInner::Any => write!(f, "/"),
            PathInner::Path(path) => write!(f, "{}", path.as_str().trim_end_matches('/')),
            PathInner::Robots => write!(f, "/robots.txt"),
        }
    }
}

impl PartialEq for DirectivePath {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (PathInner::None, _) | (_, PathInner::None) => false,
            (PathInner::Any, _) | (_, PathInner::Any) => true,
            (PathInner::Path(a), PathInner::Path(b)) => a == b,
            (PathInner::Robots, PathInner::Robots) => true,
            _ => false,
        }
    }
}

impl FromStr for DirectivePath {
    type Err = DirectivePathParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let path = s.trim();

        if path == "/" {
            return Ok(DirectivePath::ANY);
        }

        if path == "/robots.txt" || path == "robots.txt" {
            return Ok(DirectivePath::ROBOTS);
        }

        if path.is_empty() {
            return Ok(DirectivePath::NONE);
        }

        if !path.is_ascii() {
            return Err(DirectivePathParseError::InvalidCharacters);
        }

        if !path.starts_with('/') {
            return Err(DirectivePathParseError::InvalidCharacters);
        }

        if !path.chars().all(is_rfc1945_path) {
            return Err(DirectivePathParseError::InvalidPathEncoding);
        }

        Ok(DirectivePath(PathInner::Path(
            (path.to_string() + "/").as_str().into(),
        )))
    }
}

/// A directive type in a robots.txt file.
///
/// robots.txt files contain a list of directives, which can be either `Allow`, `Disallow` or an extension.
///
/// The directives control how to process the associated path.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DirectiveType {
    /// Allow the following paths
    Allow,

    /// Disallow the following paths
    Disallow,

    /// An extension directive.
    Extension(Box<str>),
}

impl fmt::Display for DirectiveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DirectiveType::Allow => write!(f, "Allow"),
            DirectiveType::Disallow => write!(f, "Disallow"),
            DirectiveType::Extension(extension) => write!(f, "{}", extension),
        }
    }
}

/// A directive in a robots.txt file, which associates a path with a directive type.
#[derive(Debug, Clone, PartialEq)]
pub struct Directive {
    path: DirectivePath,
    rule: DirectiveType,
}

impl FromStr for Directive {
    type Err = DirectiveParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let d = s.split('#').next().unwrap_or("").trim();

        let mut parts = d.splitn(2, ':');
        let rule = match parts.next() {
            Some("Allow") => DirectiveType::Allow,
            Some("Disallow") => DirectiveType::Disallow,
            Some(extension) if extension.chars().all(is_rfc1945_token) => {
                DirectiveType::Extension(extension.into())
            }
            _ => return Err(DirectiveParseError::InvalidRule),
        };

        let path: DirectivePath = match parts.next() {
            Some(path) => path.parse()?,
            None => DirectivePath::NONE,
        };

        Ok(Directive { path, rule })
    }
}

impl fmt::Display for Directive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.path.is_none() {
            // Doesn't print trailing whitespace.
            write!(f, "{}:", self.rule)
        } else {
            write!(f, "{}: {}", self.rule, self.path)
        }
    }
}

/// A set of User-Agents and associated directives.
///
/// This type represents a set of User-Agents and their associated directives in a robots.txt file.
/// Multiple User-Agents can be associated with the same directives, by listing them all in the same block.
///
/// This type is used by [`Robots`] to represent sets of rules and apply them together.`
#[derive(Debug, Clone, PartialEq)]
pub struct RobotAgent {
    agents: Vec<UserAgent>,
    directives: Vec<Directive>,
}

impl fmt::Display for RobotAgent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for agent in &self.agents {
            writeln!(f, "User-agent: {}", agent)?;
        }
        for directive in &self.directives {
            writeln!(f, "{}", directive)?;
        }
        Ok(())
    }
}

/// A robots.txt file.
///
/// The full set of rules for a robots.txt file, including wildcard directives.
///
/// This type is used to parse and apply rules to a given path and User-Agent.
///
/// # Examples
/// ```
/// use roboto::Robots;
///
/// let robots = r#"
/// User-agent: *
/// Disallow: /foo/bar
/// Allow: /hello
/// "#.parse::<Robots>().unwrap();
///
/// assert!(robots.is_allowed(&"googlebot".parse().unwrap(), "/hello"));
/// assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/foo/bar"));
///
/// let robots = r#"
/// User-agent: googlebot
/// Disallow: /foo/bar
/// "#.parse::<Robots>().unwrap();
///
/// assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/foo/bar"));
/// assert!(robots.is_allowed(&"googlebot".parse().unwrap(), "/hello"));
/// assert!(robots.is_allowed(&"bingbot".parse().unwrap(), "/foo/bar"));
///
/// ```
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Robots {
    /// Wildcard directives
    ///
    /// Stored separately because they should only be applied when
    /// no other agent matches.
    pub wildcard: Vec<Directive>,

    /// Agent-specific directives
    pub agents: Vec<RobotAgent>,
}

impl Robots {
    fn push(&mut self, mut agent: RobotAgent) {
        if agent.agents.iter().any(|a| a.is_wildcard()) {
            if self.wildcard.is_empty() {
                self.wildcard.extend(agent.directives.iter().cloned());
            }
            agent.agents.retain(|a| !a.is_wildcard());

            if !agent.agents.is_empty() {
                self.agents.push(agent);
            }
        } else {
            self.agents.push(agent);
        }
    }
}

impl FromStr for Robots {
    type Err = RobotParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut robots = Robots::default();

        let mut agents = Vec::new();
        let mut directives = Vec::new();

        for line in s.lines() {
            let line = line.split('#').next().unwrap_or("").trim();

            if line.is_empty() {
                continue;
            }

            // Case-insensitive parse of the user-agent line
            if line.to_ascii_lowercase().starts_with("user-agent") {
                if !directives.is_empty() {
                    robots.push(RobotAgent {
                        agents: agents.clone(),
                        directives: directives.clone(),
                    });
                    agents.clear();
                    directives.clear();
                }

                let agent = line.split_once(':').map(|x| x.1).unwrap_or("").trim();
                agents.push(
                    agent
                        .parse()
                        .map_err(|err| RobotParseError::InvalidUserAgent(err, agent.to_string()))?,
                );
            } else {
                directives.push(
                    line.parse()
                        .map_err(|err| RobotParseError::InvalidDirective(err, line.to_string()))?,
                );
            }
        }

        if !(agents.is_empty() && directives.is_empty()) {
            robots.push(RobotAgent {
                agents: agents.clone(),
                directives: directives.clone(),
            });
        }

        Ok(robots)
    }
}

impl fmt::Display for Robots {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((last, remainder)) = self.agents.split_last() {
            for agent in remainder {
                writeln!(f, "{}", agent)?;
            }

            write!(f, "{}", last)?;
        };

        if !self.wildcard.is_empty() {
            if !self.agents.is_empty() {
                writeln!(f)?;
            }
            writeln!(f, "User-agent: *")?;
            for directive in &self.wildcard {
                writeln!(f, "{}", directive)?;
            }
        }
        Ok(())
    }
}

impl Robots {
    /// Create a new robots.txt with a wildcard directive that disallows everything.
    pub fn deny() -> Self {
        Self {
            wildcard: vec![Directive {
                path: DirectivePath::ANY,
                rule: DirectiveType::Disallow,
            }],
            agents: Vec::new(),
        }
    }

    /// Create a new robots.txt with a wildcard directive that allows everything.
    pub fn allow() -> Self {
        Self {
            wildcard: vec![Directive {
                path: DirectivePath::ANY,
                rule: DirectiveType::Allow,
            }],
            agents: Vec::new(),
        }
    }

    /// Check if a path is allowed for a given User-Agent.
    pub fn is_allowed(&self, user_agent: &UserAgent, path: &str) -> bool {
        // robots.txt must be always allowed.
        if DirectivePath::ROBOTS.matches(path) {
            return true;
        }

        for agent in &self.agents {
            // Check if the User-Agent matches.
            if agent.agents.iter().any(|a| a == user_agent) {
                // Check all directives for the matched User-Agent.
                for directive in &agent.directives {
                    if directive.path.matches(path) {
                        match directive.rule {
                            DirectiveType::Allow => return true,
                            DirectiveType::Disallow => return false,
                            DirectiveType::Extension(_) => {}
                        }
                    }
                }

                // Checked all the rules for the matched User-Agent, so we can stop.
                return true;
            }
        }

        // User-agents which don't match any specific agent are checked against the wildcard directives.
        for directive in &self.wildcard {
            if directive.path.matches(path) {
                match directive.rule {
                    DirectiveType::Allow => return true,
                    DirectiveType::Disallow => return false,
                    DirectiveType::Extension(_) => {}
                }
            }
        }

        // By default, all pages are allowed.
        true
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use indoc::indoc;

    #[test]
    fn user_agent() {
        let ua = "Mozilla/5.0 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)";
        let ua = ua.parse::<UserAgent>().unwrap();
        assert_eq!(ua, UserAgent::ANY);
        assert_ne!(ua, "Mozilla/5.0".parse().unwrap());

        let ua = "excite".parse::<UserAgent>().unwrap();
        assert_ne!(&"googlebot".parse::<UserAgent>().unwrap(), &ua);
        let ua = "*".parse::<UserAgent>().unwrap();
        assert_eq!(&"googlebot".parse::<UserAgent>().unwrap(), &ua);
    }

    #[test]
    fn directive_path() {
        let path = "/foo/bar".parse::<DirectivePath>().unwrap();
        assert!(path.matches("/foo/bar/baz"));
        assert!(!path.matches("/foo"));

        let path = DirectivePath::ANY;
        assert!(path.matches("/foo/bar/baz"));
        assert!(path.matches("/foo"));

        let path = DirectivePath::NONE;
        assert!(!path.matches("/foo/bar/baz"));
        assert!(!path.matches("/foo"));
        assert!(!path.matches(""));
    }

    #[test]
    fn directive() {
        let directive = "Allow: /foo/bar".parse::<Directive>().unwrap();
        assert_eq!(directive.rule, DirectiveType::Allow);
        assert!(matches!(directive.path, DirectivePath(PathInner::Path(_))));
        assert!(directive.path.matches("/foo/bar/baz"));
        assert!(!directive.path.matches("/foo"));

        let directive = "Disallow: /foo/bar".parse::<Directive>().unwrap();
        assert_eq!(directive.rule, DirectiveType::Disallow);
        assert!(directive.path.matches("/foo/bar/baz"));
        assert!(!directive.path.matches("/foo"));

        let directive = "Allow: /foo/bar".parse::<Directive>().unwrap();
        assert_eq!(directive.rule, DirectiveType::Allow);
        assert!(directive.path.matches("/foo/bar/baz"));
        assert!(!directive.path.matches("/foo"));

        let directive = "Allow:".parse::<Directive>().unwrap();
        assert_eq!(directive.rule, DirectiveType::Allow);
        assert!(!directive.path.matches("/foo/bar/baz"));
        assert!(!directive.path.matches("/foo"));

        let directive = "Allow: /".parse::<Directive>().unwrap();
        assert_eq!(directive.rule, DirectiveType::Allow);
        assert!(directive.path.matches("/foo/bar/baz"));
        assert!(directive.path.matches("/foo"));
    }

    #[test]
    fn robot_txt() {
        let example = indoc! {
            r#"
      # /robots.txt for http://www.fict.org/
      # comments to webmaster@fict.org

      User-agent: unhipbot
      Disallow: /

      User-agent: webcrawler
      User-agent: excite
      Disallow:

      User-agent: *
      Disallow: /org/plans.html
      Allow: /org/
      Allow: /serv
      Allow: /~mak
      Disallow: /
            "#
        }
        .parse::<Robots>()
        .unwrap();

        assert!(!example.is_allowed(&"unhipbot".parse().unwrap(), "/org/plans.html"));
        assert!(example.is_allowed(&"unhipbot".parse().unwrap(), "/robots.txt"));

        assert!(example.is_allowed(&"webcrawler".parse().unwrap(), "/org/plans.html"));
        assert!(DirectivePath::ANY.matches("/org/plans.html"));
        assert!(example.is_allowed(&"excite".parse().unwrap(), "/org/plans.html"));

        assert!(example.is_allowed(&"googlebot".parse().unwrap(), "/org/about.html"));
        assert!(!example.is_allowed(&"googlebot".parse().unwrap(), "/org/plans.html"));
    }

    #[test]
    fn default_deny() {
        let robots = Robots::deny();
        assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/"));
        assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/foo"));
        assert!(!robots.is_allowed(&"googlebot".parse().unwrap(), "/foo/bar"));
        assert!(robots.is_allowed(&"googlebot".parse().unwrap(), "/robots.txt"));

        let expected = indoc! {
            r#"
            User-agent: *
            Disallow: /
            "#
        };

        assert_eq!(robots.to_string().trim(), expected.trim());
    }

    macro_rules! test_format {
        {$doc:tt} => {
            let expected = indoc! {
                $doc
            };

            let robots: Robots = expected.parse().unwrap();

            assert_eq!(robots.to_string(), expected);
        };
    }

    #[test]
    fn format_path() {
        test_format! {
            r#"User-agent: *
            Disallow: /foo/bar
            Allow: /hello
            "#
        };
    }

    #[test]
    fn format_blank_last() {
        test_format! {
            r#"User-agent: sus
            Allow: /boobytrap
            Disallow: /

            User-agent: cool
            Disallow: /secret
            Disallow:
            "#
        };
    }

    #[test]
    fn format_wildcard() {
        test_format! {
            r#"User-agent: sus
            Disallow: /

            User-agent: cool
            Allow:

            User-agent: *
            Disallow: /foo/bar
            Allow: /hello
            "#
        };
    }
}
