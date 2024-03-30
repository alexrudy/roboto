//! Error types for the robots.txt parser and evaluator

use std::fmt;

/// Error type for parsing a user agent
#[derive(Debug)]
pub enum UserAgentParseError {
    /// User agent is empty, not allowed
    EmptyUserAgent,

    /// User agent is not valid ascii
    InvalidUserAgentEncoding,

    /// User agent contains invalid characters
    InvalidCharacters,
}

impl fmt::Display for UserAgentParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UserAgentParseError::EmptyUserAgent => write!(f, "User agent must be non-empty"),
            UserAgentParseError::InvalidUserAgentEncoding => {
                write!(f, "User agent must be a valid ascii")
            }
            UserAgentParseError::InvalidCharacters => {
                write!(f, "User agent contains invalid characters")
            }
        }
    }
}

impl std::error::Error for UserAgentParseError {}

/// Error type for parsing a directive path
#[derive(Debug)]
pub enum DirectivePathParseError {
    /// Path is not valid ascii
    InvalidPathEncoding,

    /// Path contains invalid characters
    InvalidCharacters,
}

impl fmt::Display for DirectivePathParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DirectivePathParseError::InvalidPathEncoding => {
                write!(f, "Path must be a valid ascii")
            }
            DirectivePathParseError::InvalidCharacters => {
                write!(f, "Path contains invalid characters")
            }
        }
    }
}

impl std::error::Error for DirectivePathParseError {}

/// Error type for parsing a directive
#[derive(Debug)]
pub enum DirectiveParseError {
    /// Directive rule is invalid (e.g. missing colon, missing path, rule is a non-ascii string, etc.)
    InvalidRule,

    /// Directive path is invalid
    InvalidPath(DirectivePathParseError),
}

impl fmt::Display for DirectiveParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DirectiveParseError::InvalidRule => write!(f, "Directive rule is invalid"),
            DirectiveParseError::InvalidPath(err) => write!(f, "{}", err),
        }
    }
}

impl From<DirectivePathParseError> for DirectiveParseError {
    fn from(err: DirectivePathParseError) -> Self {
        DirectiveParseError::InvalidPath(err)
    }
}

impl std::error::Error for DirectiveParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DirectiveParseError::InvalidRule => None,
            DirectiveParseError::InvalidPath(err) => Some(err),
        }
    }
}

/// Error type for parsing a robots.txt file
#[derive(Debug)]
pub enum RobotParseError {
    /// User agent is invalid
    InvalidUserAgent(UserAgentParseError, String),

    /// Directive is invalid
    InvalidDirective(DirectiveParseError, String),
}

impl fmt::Display for RobotParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RobotParseError::InvalidUserAgent(err, agent) => {
                write!(f, "{}: {}", err, agent)
            }
            RobotParseError::InvalidDirective(err, directive) => {
                write!(f, "{}: {}", err, directive)
            }
        }
    }
}

impl std::error::Error for RobotParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            RobotParseError::InvalidUserAgent(err, _) => Some(err),
            RobotParseError::InvalidDirective(err, _) => Some(err),
        }
    }
}
